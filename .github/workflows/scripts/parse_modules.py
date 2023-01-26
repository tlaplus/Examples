"""
Parse all modules in the manifest with SANY.
"""

from concurrent.futures import ThreadPoolExecutor
import logging
import json
from os import cpu_count
from os.path import dirname
import subprocess

tlaps_modules = 'tlapm/library'
community_modules = 'CommunityModules/modules'
logging.basicConfig(level=logging.INFO)

def parse_module(module_tuple):
    """
    Parse the given module using SANY.
    """
    path, using_proofs = module_tuple
    logging.info(path)
    # If using proofs, TLAPS modules override community modules
    search_paths = ':'.join(
        [dirname(path)]
        + ([tlaps_modules] if using_proofs else [])
        + [community_modules]
    )
    sany = subprocess.run([
        'java',
        f'-DTLA-Library={search_paths}',
        '-cp', 'tla2tools.jar',
        'tla2sany.SANY', path,
    ], capture_output=True)
    sany_output = sany.stdout.decode('utf-8')
    if sany.returncode != 0 or 'Error' in sany_output or 'error' in sany_output:
        logging.error(sany_output)
        return False
    return True

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

# Skip these specs and modules as they do not currently parse
skip_specs = ['specifications/ewd998']
skip_modules = ['specifications/LoopInvariance/SumSequence.tla']

# List of all modules to parse and whether they should use TLAPS imports
modules = [
    (module['path'], any(['proof' in module['features'] for module in spec['modules']]))
    for spec in manifest['specifications'] if spec['path'] not in skip_specs
    for module in spec['modules'] if module['path'] not in skip_modules
]

# Parse specs in parallel
thread_count = cpu_count()
logging.info(f'Parsing using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(parse_module, modules)
    exit(0 if all(results) else 1)

