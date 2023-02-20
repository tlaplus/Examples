"""
Parse all modules in the manifest with SANY.
"""

from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count
from os.path import dirname, normpath
import subprocess
import tla_utils

tlaps_modules = normpath('tlapm/library')
community_modules = normpath('CommunityModules/modules')
logging.basicConfig(level=logging.INFO)

def parse_module(path):
    """
    Parse the given module using SANY.
    """
    logging.info(path)
    search_paths = ':'.join([dirname(path), tlaps_modules, community_modules])
    sany = subprocess.run([
        'java',
        '-cp', f'tla2tools.jar:{search_paths}',
        'tla2sany.SANY',
        '-error-codes',
        path
    ], capture_output=True)
    if sany.returncode != 0:
        logging.error(sany.stdout.decode('utf-8'))
        return False
    return True

manifest = tla_utils.load_manifest()

# Skip these specs and modules as they do not currently parse
skip_specs = [
    # https://github.com/tlaplus/Examples/issues/66
    'specifications/ewd998'
]
skip_modules = []

# List of all modules to parse and whether they should use TLAPS imports
modules = [
    normpath(module['path'])
    for spec in manifest['specifications'] if spec['path'] not in skip_specs
    for module in spec['modules'] if module['path'] not in skip_modules
]

# Parse specs in parallel
thread_count = cpu_count()
logging.info(f'Parsing using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(parse_module, modules)
    exit(0 if all(results) else 1)

