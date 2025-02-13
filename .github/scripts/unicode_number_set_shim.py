"""
While Unicode support in the Java tools goes through a trial period, the core
Naturals/Integers/Reals modules will remain Unicode-free. So, the Unicode
number sets ℕ, ℤ, and ℝ must be defined in any module that wishes to use
them. This script iterates through all modules in the manifest and replaces
their imports of the Naturals/Integers/Reals modules with shims containing
a definition of the Unicode number sets.
"""

from argparse import ArgumentParser
from dataclasses import dataclass
import logging
from os.path import dirname, normpath, join
import tla_utils
from typing import List
import tree_sitter_tlaplus
from tree_sitter import Language, Parser

logging.basicConfig(level=logging.INFO)

@dataclass(frozen=True)
class NumberSetShim:
    module          : str
    ascii           : str
    unicode         : str
    capture         : str
    imports         : List[str]

def shim_module_name(shim_module):
    """
    The name of the shim module.
    """
    return f'{shim_module}_UnicodeShim'

shims = [
    NumberSetShim('Naturals', 'Nat', 'ℕ', 'nat', []),
    NumberSetShim('Integers', 'Int', 'ℤ', 'int', [shim_module_name('Naturals')]),
    NumberSetShim('Reals', 'Real', 'ℝ', 'real', [shim_module_name('Integers')])
]

def build_shim_module(shim):
    """
    Derives the contents of a shim module.
    """
    module_name = shim_module_name(shim.module)
    imports = ', '.join(shim.imports + [shim.module])
    return f'---- MODULE {module_name} ----\nEXTENDS {imports}\n{shim.unicode} ≜ {shim.ascii}\n===='

def create_shim_module(module_dir, shim):
    """
    Creates a shim module for the given shim.
    """
    shim_path = join(module_dir, f'{shim_module_name(shim.module)}.tla') 
    with open(shim_path, 'w', encoding='utf-8') as module:
        module.write(build_shim_module(shim))

def create_shim_modules(examples_root, module_path):
    """
    Creates shim modules in the same directory as the module so they are
    automatically imported. Since this creates quite a few .tla files, they
    can be easily deleted with find -iname *_UnicodeShim.tla -delete.
    """
    module_path = tla_utils.from_cwd(examples_root, module_path)
    module_dir = dirname(module_path)
    for shim in shims:
        create_shim_module(module_dir, shim)

def build_imports_query(language):
    """
    Builds query to get import locations for shim insertion.
    """
    queries = [
        '(extends (identifier_ref) @import)',
        '(instance (identifier_ref) @import)'
    ]
    return language.query(' '.join(queries))

def replace_with_shim(module_bytes, node, byte_offset, shim):
    """
    Replace the text covered by the given parse tree node with a reference to
    a shim module.
    """
    source_len = node.byte_range[1] - node.byte_range[0]
    target = bytes(shim_module_name(shim.module), 'utf-8')
    target_len = len(target)
    module_bytes[node.byte_range[0]+byte_offset:node.byte_range[1]+byte_offset] = target
    return byte_offset + target_len - source_len

def replace_imports(module_bytes, tree, query):
    """
    Replaces imports with unicode shim version.
    """
    shim_modules = {shim.module : shim for shim in shims}
    imported_modules = [
        (imported_module, shim_modules[module_name])
        for imported_module in tla_utils.all_nodes_of(query.captures(tree.root_node))
        if (module_name := tla_utils.node_to_string(module_bytes, imported_module)) in shim_modules
    ]
    byte_offset = 0
    for imported_module, shim in imported_modules:
        byte_offset = replace_with_shim(module_bytes, imported_module, byte_offset, shim)

def write_module(examples_root, module_path, module_bytes):
    """
    Overwrites a module with the given bytes.
    """
    module_path = tla_utils.from_cwd(examples_root, module_path)
    with open(module_path, 'wb') as module:
        module.write(module_bytes)

if __name__ == '__main__':
    parser = ArgumentParser(description='Adds ℕ/ℤ/ℝ Unicode number set shim definitions to modules as needed.')
    parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
    parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip', required=False, default=[])
    parser.add_argument('--only', nargs='+', help='If provided, only modify models in this space-separated list', required=False, default=[])
    args = parser.parse_args()

    manifest_path = normpath(args.manifest_path)
    manifest = tla_utils.load_json(manifest_path)
    examples_root = dirname(manifest_path)
    skip_modules = args.skip
    only_modules = args.only

    TLAPLUS_LANGUAGE = Language(tree_sitter_tlaplus.language())
    parser = Parser(TLAPLUS_LANGUAGE)
    imports_query = build_imports_query(TLAPLUS_LANGUAGE)

    modules = [
        module['path']
        for spec in manifest['specifications']
        for module in spec['modules']
            if module['path'] not in skip_modules
            and (only_modules == [] or module['path'] in only_modules)
    ]

    for module_path in modules:
        logging.info(f'Processing {module_path}')
        tree, module_bytes, parse_failure = tla_utils.parse_module(examples_root, parser, module_path)
        if parse_failure:
            logging.error(f'Failed to parse {module_path}')
            exit(1)
        module_bytes = bytearray(module_bytes)
        replace_imports(module_bytes, tree, imports_query)
        write_module(examples_root, module_path, module_bytes)
        create_shim_modules(examples_root, module_path)

