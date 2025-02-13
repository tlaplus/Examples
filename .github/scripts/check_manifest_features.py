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
import logging
import glob
from os.path import basename, dirname, normpath, splitext
from typing import Any
import re
import tla_utils
import tree_sitter_tlaplus
from tree_sitter import Language, Parser

logging.basicConfig(level=logging.INFO)

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
        + '(cdot) @action_composition'
    )

    return Queries(import_query, module_name_query, feature_query)

def get_module_names_in_dir(examples_root, dir):
    """
    Gets the module names of all .tla files in the given directory.
    """
    module_paths = glob.glob(f'{dir}/*.tla', root_dir=examples_root)
    return set([splitext(basename(path))[0] for path in module_paths])

def get_tree_features(tree, queries):
    """
    Returns any notable features in the parse tree, such as pluscal or proofs
    """
    return set([
        capture_name.replace('_', ' ')
        for capture_name, _
        in queries.features.captures(tree.root_node).items()
    ])

def get_module_features(examples_root, path, parser, queries):
    """
    Gets notable features for the .tla file at the given path
    """
    tree, _, _ = tla_utils.parse_module(examples_root, parser, path)
    return get_tree_features(tree, queries)

# Regexes mapping to features for models
model_features = {
    re.compile('^PROPERTY', re.MULTILINE) : 'liveness',
    re.compile('^PROPERTIES', re.MULTILINE): 'liveness',
    re.compile('^SYMMETRY', re.MULTILINE): 'symmetry',
    re.compile('^ALIAS', re.MULTILINE): 'alias',
    re.compile('^VIEW', re.MULTILINE): 'view',
    re.compile('^CONSTRAINT', re.MULTILINE): 'state constraint',
    re.compile('^CONSTRAINTS', re.MULTILINE): 'state constraint',
    re.compile('^CHECK_DEADLOCK\\s+FALSE', re.MULTILINE) : 'ignore deadlock'
}

def get_model_features(examples_root, path):
    """
    Finds features present in the given .cfg model file.
    This will be a best-effort regex search until a tree-sitter grammar is
    created for .cfg files.
    """
    path = tla_utils.from_cwd(examples_root, path)
    features = []
    model_text = None
    with open(path, 'rt') as model_file:
        model_text = model_file.read()
    for regex, feature in model_features.items():
        if regex.search(model_text):
            features.append(feature)
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
    'Toolbox',
    'Apalache'
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

def get_community_imports(examples_root, tree, text, dir, has_proof, queries):
    """
    Gets all modules imported by a given .tla file that are not standard
    modules or modules in the same file or directory. Community module
    imports are what's left.
    """
    imports = set(
        [
            tla_utils.node_to_string(text, node)
            for node in tla_utils.all_nodes_of(queries.imports.captures(tree.root_node))
        ]
    )
    modules_in_file = set(
        [
            tla_utils.node_to_string(text, node)
            for node in tla_utils.all_nodes_of(queries.module_names.captures(tree.root_node))
        ]
    )
    imports = (
        imports
        - modules_in_file
        - tlc_modules
        - tlaps_modules
        - get_module_names_in_dir(examples_root, dir)
    )
    return imports - tlaps_module_overloads if has_proof else imports
 
def get_community_module_imports(examples_root, parser, path, queries):
    """
    Gets all community modules imported by the .tla file at the given path.
    """
    tree, text, _ = tla_utils.parse_module(examples_root, parser, path)
    has_proof = 'proof' in get_tree_features(tree, queries)
    return get_community_imports(examples_root, tree, text, dirname(path), has_proof, queries)

def check_features(parser, queries, manifest, examples_root):
    """
    Validates every field of the manifest that can be validated.
    """
    success = True
    for spec in manifest['specifications']:
        if spec['title'] == '':
            success = False
            logging.error(f'Spec {spec["path"]} does not have a title')
        if spec['description'] == '':
            success = False
            logging.error(f'Spec {spec["path"]} does not have a description')
        if not any(spec['authors']):
            success = False
            logging.error(f'Spec {spec["path"]} does not have any listed authors')
        for module in spec['modules']:
            module_path = module['path']
            tree, text, parse_err = tla_utils.parse_module(examples_root, parser, module_path)
            if parse_err:
                success = False
                logging.error(f'Module {module["path"]} contains syntax errors')
            expected_features = get_tree_features(tree, queries)
            actual_features = set(module['features'])
            if expected_features != actual_features:
                success = False
                logging.error(
                    f'Module {module["path"]} has incorrect features in manifest; '
                    + f'expected {list(expected_features)}, actual {list(actual_features)}'
                )
            expected_imports = get_community_imports(examples_root, tree, text, dirname(module_path), 'proof' in expected_features, queries)
            actual_imports = set(module['communityDependencies'])
            if expected_imports != actual_imports:
                success = False
                logging.error(
                    f'Module {module["path"]} has incorrect community dependencies in manifest; '
                    + f'expected {list(expected_imports)}, actual {list(actual_imports)}'
                )
            for model in module['models']:
                expected_features = get_model_features(examples_root, model['path'])
                actual_features = set(model['features'])
                if expected_features != actual_features:
                    success = False
                    logging.error(
                        f'Model {model["path"]} has incorrect features in manifest; '
                        + f'expected {list(expected_features)}, actual {list(actual_features)}'
                    )
                if tla_utils.has_state_count(model) and not tla_utils.is_state_count_valid(model):
                    success = False
                    logging.error(
                        f'Model {model["path"]} has state count info recorded; this is '
                        + 'only valid for exhaustive search models that complete successfully.'
                    )

    return success

if __name__ == '__main__':
    parser = ArgumentParser(description='Checks metadata in tlaplus/examples manifest.json against module and model files in repository.')
    parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
    args = parser.parse_args()

    manifest_path = normpath(args.manifest_path)
    manifest = tla_utils.load_json(manifest_path)
    examples_root = dirname(manifest_path)

    TLAPLUS_LANGUAGE = Language(tree_sitter_tlaplus.language())
    parser = Parser(TLAPLUS_LANGUAGE)
    queries = build_queries(TLAPLUS_LANGUAGE)

    if check_features(parser, queries, manifest, examples_root):
        logging.info('SUCCESS: metadata in manifest is correct')
        exit(0)
    else:
        logging.error("Metadata in manifest is incorrect")
        exit(1)

