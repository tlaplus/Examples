"""
This script performs whatever validations are possible on the metadata in
the manifest.json file. Prominent checks include:
 * .tla files containing pluscal or proofs are marked as such
 * .tla files importing community modules have those modules listed
 * .cfg files with certain features are marked as such
 * Human-written fields are not empty
"""

from argparse import ArgumentParser
from dataclasses import dataclass
import glob
from os.path import basename, dirname, join, normpath, splitext
from typing import Any
import tla_utils
from tree_sitter import Language, Parser

def build_ts_grammar(ts_path):
    """
    Builds the tree-sitter-tlaplus grammar and constructs the parser.
    """
    ts_build_path = join(ts_path, 'build', 'tree-sitter-languages.so')
    Language.build_library(ts_build_path, [ts_path])
    TLAPLUS_LANGUAGE = Language(ts_build_path, 'tlaplus')
    parser = Parser()
    parser.set_language(TLAPLUS_LANGUAGE)
    return (TLAPLUS_LANGUAGE, parser)

@dataclass
class Queries:
    imports         : Any
    module_names    : Any
    features        : Any

def build_queries(language):
    """
    Builds queries for the TLA+ tree-sitter language.
    """
    # Query finding all module imports in a .tla file
    import_query = language.query(
        '(extends (identifier_ref) @extends)'
        + '(instance (identifier_ref) @instance)'
    )

    # Query finding all defined module names in a .tla file
    # Especially useful for finding nested module names
    module_name_query = language.query(
        '(module name: (identifier) @module_name)'
    )

    # This query looks for pluscal and proof constructs
    # It can be extended to look for other things if desired
    feature_query = language.query(
        '(pcal_algorithm_start) @pluscal'
        + '[(terminal_proof) (non_terminal_proof)] @proof'
    )

    return Queries(import_query, module_name_query, feature_query)

def parse_module(parser, path):
    """
    Parses a .tla file; returns the parse tree along with whether a parse
    error was detected.
    """
    module_text = None
    with open(path, 'rb') as module_file:
        module_text = module_file.read()
    tree = parser.parse(module_text)
    return (tree, module_text, tree.root_node.has_error)

def get_module_names_in_dir(dir):
    """
    Gets the module names of all .tla files in the given directory.
    """
    return set([splitext(basename(path))[0] for path in glob.glob(f'{dir}/*.tla')])

def get_tree_features(tree, queries):
    """
    Returns any notable features in the parse tree, such as pluscal or proofs
    """
    return set([name for _, name in queries.features.captures(tree.root_node)])

def get_module_features(root_dir, path, parser, queries):
    """
    Gets notable features for the .tla file at the given path
    """
    path = tla_utils.from_cwd(root_dir, path)
    tree, _, _ = parse_module(parser, path)
    return get_tree_features(tree, queries)

# Keywords mapping to features for models
model_features = {
    'PROPERTY': 'liveness',
    'PROPERTIES': 'liveness',
    'SYMMETRY': 'symmetry',
    'ALIAS': 'alias',
    'VIEW': 'view',
    'CONSTRAINT': 'state constraint',
    'CONSTRAINTS': 'state constraint',
}

def get_model_features(examples_root, path):
    """
    Finds features present in the given .cfg model file.
    This will be a best-effort text search until a tree-sitter grammar is
    created for .cfg files.
    """
    path = tla_utils.from_cwd(examples_root, path)
    features = []
    model_text = None
    with open(path, 'rt') as model_file:
        model_text = model_file.read()
    for line in model_text.split('\n'):
        tokens = line.split()
        if len(tokens) > 0 and tokens[0] in model_features:
            features.append(model_features[tokens[0]])
    return set(features)

# All the standard modules available when using TLC
tlc_modules = {
    'Bags',
    'FiniteSets',
    'Integers',
    'Json',
    'Naturals',
    'Randomization',
    'RealTime',
    'Reals',
    'Sequences',
    'TLC',
    'TLCExt',
    'Toolbox'
}

# All the standard modules available when using TLAPS
tlaps_modules = {
    'BagsTheorems',
    'FiniteSetTheorems',
    'FunctionTheorems',
    'NaturalsInduction',
    'SequencesExtTheorems',
    'SequenceTheorems',
    'TLAPS',
    'WellFoundedInduction'
}

# Modules overloaded by TLAPS; some of these are ordinarily imported as
# community modules.
tlaps_module_overloads = {
    'Bags',
    'FiniteSets',
    'Functions',
    'RealTime',
    'SequencesExt'
}

def get_community_imports(tree, text, dir, has_proof, queries):
    """
    Gets all modules imported by a given .tla file that are not standard
    modules or modules in the same file or directory. Community module
    imports are what's left.
    """
    imports = set(
        [
            text[node.start_byte:node.end_byte].decode('utf-8')
            for node, _ in queries.imports.captures(tree.root_node)
        ]
    )
    modules_in_file = set(
        [
            text[node.start_byte:node.end_byte].decode('utf-8')
            for node, _ in queries.module_names.captures(tree.root_node)
        ]
    )
    imports = (
        imports
        - modules_in_file
        - tlc_modules
        - tlaps_modules
        - get_module_names_in_dir(dir)
    )
    return imports - tlaps_module_overloads if has_proof else imports
 
def get_community_module_imports(examples_root, parser, path, queries):
    """
    Gets all community modules imported by the .tla file at the given path.
    """
    path = tla_utils.from_cwd(examples_root, path)
    tree, text, _ = parse_module(parser, path)
    dir = dirname(path)
    has_proof = 'proof' in get_tree_features(tree, queries)
    return get_community_imports(tree, text, dir, has_proof, queries)

def check_features(parser, queries, manifest, examples_root):
    """
    Validates every field of the manifest that can be validated.
    """
    success = True
    for spec in manifest['specifications']:
        if spec['title'] == '':
            success = False
            print(f'ERROR: Spec {spec["path"]} does not have a title')
        if spec['description'] == '':
            success = False
            print(f'ERROR: Spec {spec["path"]} does not have a description')
        if not any(spec['authors']):
            success = False
            print(f'ERROR: Spec {spec["path"]} does not have any listed authors')
        for module in spec['modules']:
            module_path = tla_utils.from_cwd(examples_root, module['path'])
            tree, text, parse_err = parse_module(parser, module_path)
            if parse_err:
                success = False
                print(f'ERROR: Module {module["path"]} contains syntax errors')
            expected_features = get_tree_features(tree, queries)
            actual_features = set(module['features'])
            if expected_features != actual_features:
                success = False
                print(
                    f'ERROR: Module {module["path"]} has incorrect features in manifest; '
                    + f'expected {list(expected_features)}, actual {list(actual_features)}'
                )
            module_dir = tla_utils.from_cwd(examples_root, dirname(module['path']))
            expected_imports = get_community_imports(tree, text, module_dir, 'proof' in expected_features, queries)
            actual_imports = set(module['communityDependencies'])
            if expected_imports != actual_imports:
                success = False
                print(
                    f'ERROR: Module {module["path"]} has incorrect community dependencies in manifest; '
                    + f'expected {list(expected_imports)}, actual {list(actual_imports)}'
                )
            for model in module['models']:
                expected_features = get_model_features(examples_root, model['path'])
                actual_features = set(model['features'])
                if expected_features != actual_features:
                    success = False
                    print(
                        f'ERROR: Model {model["path"]} has incorrect features in manifest; '
                        + f'expected {list(expected_features)}, actual {list(actual_features)}'
                    )
    return success

if __name__ == '__main__':
    parser = ArgumentParser(description='Checks metadata in tlaplus/examples manifest.json against module and model files in repository.')
    parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
    parser.add_argument('--ts_path', help='Path to tree-sitter-tlaplus directory', required=True)
    args = parser.parse_args()

    manifest_path = normpath(args.manifest_path)
    manifest = tla_utils.load_json(manifest_path)
    examples_root = dirname(manifest_path)

    (TLAPLUS_LANGUAGE, parser) = build_ts_grammar(normpath(args.ts_path))
    queries = build_queries(TLAPLUS_LANGUAGE)

    if check_features(parser, queries, manifest, examples_root):
        print('SUCCESS: metadata in manifest is correct')
        exit(0)
    else:
        print("ERROR: metadata in manifest is incorrect")
        exit(1)

