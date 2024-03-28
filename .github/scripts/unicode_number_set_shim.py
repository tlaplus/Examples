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

logging.basicConfig(level=logging.INFO)

@dataclass(frozen=True)
class NumberSetShim:
    module          : str
    ascii           : str
    unicode         : str
    capture         : str

shims = [
    NumberSetShim('Naturals', 'Nat', 'ℕ', 'nat'),
    NumberSetShim('Integers', 'Int', 'ℤ', 'int'),
    NumberSetShim('Reals', 'Real', 'ℝ', 'real')
]

def shim_module_name(shim):
    return f'{shim.module}_UnicodeShim'

def build_shim_module(shim):
    return f'---- MODULE {shim_module_name(shim)} ----\nEXTENDS {shim.module}\n{shim.unicode} ≜ {shim.ascii}\n===='

def create_shim_module(module_dir, shim):
    with open(join(module_dir, f'{shim_module_name(shim)}.tla'), 'w', encoding='utf-8') as module:
        module.write(build_shim_module(shim))

def build_imports_query(language):
    """
    Builds query to get import locations for shim insertion.
    """
    queries = [
        '(extends) @extends',
        '(module (instance) @instance)',
        '(module (local_definition (instance) @instance))',
        '(module_definition (instance) @instance)'
    ]
    return language.query(' '.join(queries))

def node_to_string(module_bytes, node, byte_offset):
    return module_bytes[node.byte_range[0]+byte_offset:node.byte_range[1]+byte_offset].decode('utf-8')

def replace_with_shim(module_bytes, node, byte_offset, shim):
    target = bytes(shim_module_name(shim), 'utf-8')
    target_len = len(target)
    source_len = node.byte_range[1] - node.byte_range[0]
    module_bytes[node.byte_range[0]+byte_offset:node.byte_range[1]+byte_offset] = target
    return byte_offset + target_len - source_len

def replace_imports(module_bytes, tree, query):
    """
    Replaces imports with unicode shim version.
    """
    shim_modules = {shim.module : shim for shim in shims}
    captures = query.captures(tree.root_node)
    byte_offset = 0
    for node, capture_name in captures:
        match capture_name:
            case 'extends':
                for imported_module in node.named_children:
                    imported_module_name = node_to_string(module_bytes, imported_module, byte_offset)
                    if imported_module_name in shim_modules:
                        shim = shim_modules[imported_module_name]
                        byte_offset = replace_with_shim(module_bytes, imported_module, byte_offset, shim)
            case 'instance':
                imported_module = node.named_child(0)
                imported_module_name = node_to_string(module_bytes, imported_module, byte_offset)
                if imported_module_name in shim_modules:
                    shim = shim_modules[imported_module_name]
                    byte_offset = replace_with_shim(module_bytes, imported_module, byte_offset, shim)
            case _:
                logging.error(f'Unknown capture {capture_name}')
                exit(1)

def write_module(examples_root, module_path, module_bytes):
    module_path = tla_utils.from_cwd(examples_root, module_path)
    with open(module_path, 'wb') as module:
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
    imports_query = build_imports_query(TLAPLUS_LANGUAGE)

    modules = [
        module['path']
        for spec in manifest['specifications']
        for module in spec['modules']
            if normpath(module['path']) not in skip_modules
            and (only_modules == [] or normpath(module['path']) in only_modules)
    ]

    for module_path in modules:
        logging.info(f'Processing {module_path}')
        tree, module_bytes, parse_failure = tla_utils.parse_module(examples_root, parser, module_path)
        module_bytes = bytearray(module_bytes)
        if parse_failure:
            logging.error(f'Failed to parse {module_path}')
            exit(1)
        replace_imports(module_bytes, tree, imports_query)
        write_module(examples_root, module_path, module_bytes)

