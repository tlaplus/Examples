"""
Converts all TLA⁺ modules from ASCII to Unicode or vice-versa.
"""

from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count
from os.path import dirname, normpath
import subprocess
from subprocess import CompletedProcess
import tla_utils

parser = ArgumentParser(description='Converts all TLA+ modules from ASCII to Unicode or vice-versa.')
parser.add_argument('--tlauc_path', help='Path to the TLAUC executable', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--to_ascii', help='Convert to ASCII instead of Unicode', action='store_true')
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip converting', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only convert models in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
args = parser.parse_args()

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

tlauc_path = normpath(args.tlauc_path)
to_ascii = args.to_ascii
manifest_path = normpath(args.manifest_path)
examples_root = dirname(manifest_path)
skip_modules = args.skip
only_modules = args.only

manifest = tla_utils.load_json(manifest_path)

# List of all modules to convert
modules = [
    tla_utils.from_cwd(examples_root, module['path'])
    for spec in manifest['specifications']
    for module in spec['modules']
        if module['path'] not in skip_modules
        and (only_modules == [] or module['path'] in only_modules)
]

for path in skip_modules:
    logging.info(f'Skipping {path}')

def convert_module(module_path):
    logging.info(f'Converting {module_path}')
    result = subprocess.run(
        [tlauc_path, module_path] + (['--ascii'] if to_ascii else []),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True
    )
    match result:
        case CompletedProcess():
            if result.returncode == 0:
                logging.debug(result.stdout)
                return True
            else:
                logging.error(f'Module {module_path} conversion failed with return code {result.returncode}; output:\n{result.stdout}')
                return False
        case _:
            logging.error(f'Unhandled TLAUC result type {type(result)}: {result.stdout}')
            return False

success = True
thread_count = cpu_count() if not args.verbose else 1
logging.info(f'Converting specs to {"ASCII" if to_ascii else "Unicode"} using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(convert_module, modules)
    exit(0 if all(results) else 1)

