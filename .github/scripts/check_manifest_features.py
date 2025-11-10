"""
This script performs whatever validations are possible on the metadata in
the manifest.json files. Prominent checks include:
 * .tla files containing pluscal or proofs are marked as such
 * Model state counts are applicable to the model type
 * Human-written fields such as authorship are not empty
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

def check_features(parser, queries, manifest, examples_root):
    """
    Validates every field of the manifest that can be validated.
    """
    success = True
    for path, spec in manifest:
        if not any(spec['authors']):
            success = False
            logging.error(f'Spec {path} does not have any listed authors')
        for module in spec['modules']:
            module_path = module['path']
            tree, text, parse_err = tla_utils.parse_module(examples_root, parser, module_path)
            if parse_err:
                success = False
                logging.error(f'Module {module["path"]} contains syntax errors')
            module_features = get_tree_features(tree, queries)
            expected_features = module_features - {'proof'}
            actual_features = set(module['features'])
            if expected_features != actual_features:
                success = False
                logging.error(
                    f'Module {module["path"]} has incorrect features in manifest; '
                    + f'expected {list(expected_features)}, actual {list(actual_features)}'
                )
            if 'proof' in module_features and 'proof' not in module:
                success = False
                logging.error(f'Module {module["path"]} contains proof but no proof runtime details in manifest')
            for model in module['models']:
                if tla_utils.has_state_count(model) and not tla_utils.is_state_count_valid(model):
                    success = False
                    logging.error(
                        f'Model {model["path"]} has state count info recorded; this is '
                        + 'only valid for exhaustive search models that complete successfully.'
                    )

    return success

if __name__ == '__main__':
    parser = ArgumentParser(description='Checks metadata in manifest.json files against module and model files in repository.')
    parser.add_argument('--examples_root', help='Root directory of the tlaplus/examples repository', required=False, default='.')
    args = parser.parse_args()

    manifest = tla_utils.load_all_manifests(args.examples_root)

    TLAPLUS_LANGUAGE = Language(tree_sitter_tlaplus.language())
    parser = Parser(TLAPLUS_LANGUAGE)
    queries = build_queries(TLAPLUS_LANGUAGE)

    if check_features(parser, queries, manifest, args.examples_root):
        logging.info('SUCCESS: metadata in manifest is correct')
        exit(0)
    else:
        logging.error("Metadata in manifest is incorrect")
        exit(1)

