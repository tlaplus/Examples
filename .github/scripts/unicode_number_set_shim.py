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

def build_number_set_query(language):
    """
    Builds query looking for use of number sets.
    """
    return language.query(' '.join([f'({shim.capture}_number_set "{shim.unicode}") @{shim.capture}' for shim in shims]))

def build_insertion_point_query(language):
    """
    Builds query to get insertion point for shim definitions.
    """
    return language.query('((header_line) name: (identifier) (header_line)) @header (extends) @extends')

def get_required_defs(tree, query):
    return set([name for _, name in query.captures(tree.root_node)])

def get_def_text(required_defs):
    defs = '\n'
    for shim in shims:
        if shim.capture in required_defs:
            defs += f'LOCAL {shim.unicode} ≜ {shim.ascii}\n'
    return defs

def get_insertion_point(tree, query):
    captures = query.captures(tree.root_node)
    has_extends = any(name for (_, name) in captures if name == 'extends')
    if has_extends:
        extends_node = next(node for (node, name) in captures if name == 'extends')
        return extends_node.byte_range[1]
    else:
        header = next(node for (node, name) in captures if name == 'header')
        return header.byte_range[1]

def insert_defs(module_path, insertion_point, defs):
    def_bytes = bytes(defs, 'utf-8')
    with open(module_path, 'rb+') as module:
        module_bytes = bytearray(module.read())
        module_bytes[insertion_point:insertion_point] = def_bytes
        module.write(module_bytes)

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
    number_set_query = build_number_set_query(TLAPLUS_LANGUAGE)
    insertion_point_query = build_insertion_point_query(TLAPLUS_LANGUAGE)

    modules = [
        module['path']
        for spec in manifest['specifications']
        for module in spec['modules']
            if normpath(module['path']) not in skip_modules
            and (only_modules == [] or normpath(module['path']) in only_modules)
    ]

    for module_path in modules:
        logging.info(f'Processing {module_path}')
        tree, _, _ = tla_utils.parse_module(examples_root, parser, module_path)
        required_defs = get_required_defs(tree, number_set_query)
        if not any(required_defs):
            logging.info('No shim insertion necessary')
            continue
        logging.info(f'Inserting defs {required_defs}')
        defs = get_def_text(required_defs)
        insertion_point = get_insertion_point(tree, insertion_point_query)
        insert_defs(module_path, insertion_point, defs)

