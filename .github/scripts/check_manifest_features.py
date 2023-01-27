"""
This script performs whatever validations are possible on the metadata in
the manifest.json file. Prominent checks include:
 * .tla files containing pluscal or proofs are marked as such
 * .tla files importing community modules have those modules listed
 * .cfg files with certain features are marked as such
 * Human-written fields are not empty
"""

import glob
import json
from os.path import basename, dirname, splitext
from tree_sitter import Language, Parser

# Builds the tree-sitter-tlaplus grammar and constructs the parser
Language.build_library(
  'build/tree-sitter-languages.so',
  ['tree-sitter-tlaplus']
)

TLAPLUS_LANGUAGE = Language('build/tree-sitter-languages.so', 'tlaplus')
parser = Parser()
parser.set_language(TLAPLUS_LANGUAGE)

def parse_module(path):
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

# This query looks for pluscal and proof constructs
# It can be extended to look for other things if desired
feature_query = TLAPLUS_LANGUAGE.query(
    '(pcal_algorithm_start) @pluscal'
    + '[(terminal_proof) (non_terminal_proof)] @proof'
)

def get_tree_features(tree):
    """
    Returns any notable features in the parse tree, such as pluscal or proofs
    """
    return set([name for _, name in feature_query.captures(tree.root_node)])

def get_module_features(path):
    """
    Gets notable features for the .tla file at the given path
    """
    tree, _, _ = parse_module(path)
    return get_tree_features(tree)

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

def get_model_features(path):
    """
    Finds features present in the given .cfg model file.
    This will be a best-effort text search until a tree-sitter grammar is
    created for .cfg files.
    """
    features = []
    model_text = None
    with open(path, 'rt') as model_file:
        model_text = model_file.read()
    for line in model_text.split('\n'):
        tokens = line.split()
        if len(tokens) > 0 and tokens[0] in model_features:
            features.append(model_features[tokens[0]])
    return set(features)

# Query finding all module imports in a .tla file
import_query = TLAPLUS_LANGUAGE.query(
    '(extends (identifier_ref) @extends)'
    + '(instance (identifier_ref) @instance)'
)

# Query finding all defined module names in a .tla file
# Especially useful for finding nested module names
module_name_query = TLAPLUS_LANGUAGE.query(
    '(module name: (identifier) @module_name)'
)

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

def get_community_imports(tree, text, dir, has_proof):
    """
    Gets all modules imported by a given .tla file that are not standard
    modules or modules in the same file or directory. Community module
    imports are what's left.
    """
    imports = set(
        [
            text[node.start_byte:node.end_byte].decode('utf-8')
            for node, _ in import_query.captures(tree.root_node)
        ]
    )
    modules_in_file = set(
        [
            text[node.start_byte:node.end_byte].decode('utf-8')
            for node, _ in module_name_query.captures(tree.root_node)
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

def get_community_module_imports(path):
    """
    Gets all community modules imported by the .tla file at the given path.
    """
    tree, text, _ = parse_module(path)
    dir = dirname(path)
    has_proof = 'proof' in get_tree_features(tree)
    return get_community_imports(tree, text, dir, has_proof)

if __name__ == '__main__':
    manifest = None
    with open('manifest.json', 'rt') as manifest_file:
        manifest = json.load(manifest_file)

    # Validates every field of the manifest that can be validated.
    success = True
    for spec in manifest['specifications']:
        if spec['title'] == '':
            success = False
            print(f'Spec {spec["path"]} does not have a title')
        if spec['description'] == '':
            success = False
            print(f'Spec {spec["path"]} does not have a description')
        if not any(spec['authors']):
            success = False
            print(f'Spec {spec["path"]} does not have any listed authors')
        for module in spec['modules']:
            tree, text, parse_err = parse_module(module['path'])
            if parse_err:
                success = False
                print(f'Module {module["path"]} contains syntax errors')
            expected_features = get_tree_features(tree)
            actual_features = set(module['features'])
            if expected_features != actual_features:
                success = False
                print(
                    f'Module {module["path"]} has incorrect features in manifest; '
                    + f'expected {list(expected_features)}, actual {list(actual_features)}'
                )
            expected_imports = get_community_imports(tree, text, dirname(module['path']), 'proof' in expected_features)
            actual_imports = set(module['communityDependencies'])
            if expected_imports != actual_imports:
                success = False
                print(
                    f'Module {module["path"]} has incorrect community dependencies in manifest; '
                    + f'expected {list(expected_imports)}, actual {list(actual_imports)}'
                )
            for model in module['models']:
                expected_features = get_model_features(model['path'])
                actual_features = set(model['features'])
                if expected_features != actual_features:
                    success = False
                    print(
                        f'Model {model["path"]} has incorrect features in manifest; '
                        + f'expected {list(expected_features)}, actual {list(actual_features)}'
                    )

    exit(0 if success else 1)

