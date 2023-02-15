"""
Parse all modules in the manifest with SANY.
"""

from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count, pathsep
from os.path import dirname, normpath
import subprocess
import tla_utils

tlaps_modules = normpath('tlapm/library')
community_modules = normpath('CommunityModules/modules')
logging.basicConfig(level=logging.INFO)

def parse_module(module_tuple):
    """
    Parse the given module using SANY.
    """
    path, using_proofs = module_tuple
    logging.info(path)
    # If using proofs, TLAPS modules override community modules
    search_paths = pathsep.join(
        [dirname(path)]
        + ([tlaps_modules] if using_proofs else [])
        + [community_modules]
    )
    sany = subprocess.run([
        'java',
        f'-DTLA-Library={search_paths}',
        '-cp', 'tla2tools.jar',
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
skip_specs = ['specifications/ewd998']
skip_modules = []

# List of all modules to parse and whether they should use TLAPS imports
modules = [
    (normpath(module['path']), any(['proof' in module['features'] for module in spec['modules']]))
    for spec in manifest['specifications'] if spec['path'] not in skip_specs
    for module in spec['modules'] if module['path'] not in skip_modules
]

# Parse specs in parallel
thread_count = cpu_count()
logging.info(f'Parsing using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(parse_module, modules)
    exit(0 if all(results) else 1)

