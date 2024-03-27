"""
While Unicode support in the Java tools goes through a trial period, the core
Naturals/Integers/Reals modules will remain Unicode-free. So, the Unicode
number sets ℕ, ℤ, and ℝ must be defined in any module that wishes to use
them. This script iterates through all modules in the manifest and detects
whether they reference the Unicode number sets; if so, a local definition of
the relevant Unicode number set is inserted into the top of the file.
"""

from argparse import ArgumentParser
from dataclasses import dataclass
import logging
from os.path import dirname, join, normpath
import tla_utils
from tree_sitter import Language, Parser

logging.basicConfig(level=logging.INFO)

@dataclass
class NumberSetShim:
    ascii           : str
    unicode         : str
    capture         : str

shims = [
    NumberSetShim('Nat', 'ℕ', 'nat'),
    NumberSetShim('Int', 'ℤ', 'int'),
    NumberSetShim('Real', 'ℝ', 'real')
]

def build_query(language):
    """
    Builds number set shim query.
    """
    return language.query(' '.join([f'({shim.capture}_number_set "{shim.unicode}") @{shim.capture}' for shim in shims]))

def get_required_defs(examples_root, parser, path, query):
    tree, _, _ = tla_utils.parse_module(examples_root, parser, path)
    return set([name for _, name in query.features.captures(tree.root_node)])

if __name__ == '__main__':
    parser = ArgumentParser(description='Adds ℕ/ℤ/ℝ Unicode number set shim definitions to modules as needed.')
    parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
    parser.add_argument('--ts_path', help='Path to tree-sitter-tlaplus directory', required=True)
    parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip', required=False, default=[])
    parser.add_argument('--only', nargs='+', help='If provided, only modify models in this space-separated list', required=False, default=[])
    args = parser.parse_args()

    manifest_path = normpath(args.manifest_path)
    manifest = tla_utils.load_json(manifest_path)
    examples_root = dirname(manifest_path)
    skip_modules = [normpath(path) for path in args.skip]
    only_modules = [normpath(path) for path in args.only]

    (TLAPLUS_LANGUAGE, parser) = tla_utils.build_ts_grammar(normpath(args.ts_path))
    query = build_query(TLAPLUS_LANGUAGE)

    modules = [
        module['path']
        for spec in manifest['specifications']
        for module in spec['modules']
            if normpath(module['path']) not in skip_modules
            and (only_modules == [] or normpath(module['path']) in only_modules)
    ]

    for module_path in modules:
        logging.info(f'Processing {module_path}')
        required_defs = get_required_defs(examples_root, parser, module_path, query)
        logging.info(f'Require {required_defs}')

