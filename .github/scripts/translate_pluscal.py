"""
Runs PlusCal translation on all PlusCal specs.
"""

from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count
from os.path import dirname, normpath
import subprocess
from subprocess import CompletedProcess
import tla_utils

parser = ArgumentParser(description='Run PlusCal translation on all modules.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip converting', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only convert models in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
parser.add_argument('--enable_assertions', help='Enable Java assertions (pass -enableassertions to JVM)', action='store_true')
args = parser.parse_args()

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

tools_path = normpath(args.tools_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root = dirname(manifest_path)
skip_modules = args.skip
only_modules = args.only
enable_assertions = args.enable_assertions

manifest = tla_utils.load_json(manifest_path)

# List of all modules to translate
modules = [
    tla_utils.from_cwd(examples_root, module['path'])
    for spec in manifest['specifications']
    for module in spec['modules']
        if 'pluscal' in module['features']
        and module['path'] not in skip_modules
        and (only_modules == [] or module['path'] in only_modules)
]

for path in skip_modules:
    logging.info(f'Skipping {path}')

def translate_module(module_path):
    logging.info(f'Translating {module_path}')
    jvm_parameters = ['-cp', tools_path] + (['-enableassertions'] if enable_assertions else [])
    pcal_parameters = ['-nocfg', module_path]
    pcal = subprocess.run(
        ['java'] + jvm_parameters + ['pcal.trans'] + pcal_parameters,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True
    )
    output = ' '.join(pcal.args) + '\n' + pcal.stdout
    if 0 == pcal.returncode:
        logging.debug(output)
        return True
    else:
        logging.error(output)
        return False

success = True
thread_count = cpu_count() if not args.verbose else 1
logging.info(f'Translating PlusCal using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(translate_module, modules)
    exit(0 if all(results) else 1)

