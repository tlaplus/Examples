"""
Parse all modules in the manifest with SANY.
"""

from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count
from os.path import dirname, normpath, pathsep
import subprocess
import tla_utils

parser = ArgumentParser(description='Parses all TLA+ modules in the tlaplus/examples repo using SANY.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=True)
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip parsing', required=False, default=[])
args = parser.parse_args()

logging.basicConfig(level=logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
tlaps_modules = normpath(args.tlapm_lib_path)
community_modules = normpath(args.community_modules_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root = dirname(manifest_path)
skip_modules = [normpath(path) for path in args.skip]

def parse_module(path):
    """
    Parse the given module using SANY.
    """
    logging.info(path)
    # Jar paths must go first
    search_paths = pathsep.join([tools_jar_path, community_modules, dirname(path), tlaps_modules])
    sany = subprocess.run([
        'java',
        '-cp', search_paths,
        'tla2sany.SANY',
        '-error-codes',
        path
    ], capture_output=True)
    if sany.returncode != 0:
        logging.error(sany.stdout.decode('utf-8'))
        return False
    return True

manifest = tla_utils.load_json(manifest_path)

# List of all modules to parse and whether they should use TLAPS imports
modules = [
    tla_utils.from_cwd(examples_root, module['path'])
    for spec in manifest['specifications']
    for module in spec['modules']
        if normpath(module['path']) not in skip_modules
]

for path in skip_modules:
    logging.info(f'Skipping {path}')

# Parse specs in parallel
thread_count = cpu_count()
logging.info(f'Parsing using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(parse_module, modules)
    exit(0 if all(results) else 1)

