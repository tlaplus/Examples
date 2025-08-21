"""
Parse all modules in the manifests with SANY.
"""

from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import logging
from os import cpu_count
from os.path import join, dirname, normpath, pathsep
import subprocess
import tla_utils

parser = ArgumentParser(description='Parses all TLA+ modules in the tlaplus/examples repo using SANY.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=False, default='deps/tools/tla2tools.jar')
parser.add_argument('--apalache_path', help='Path to the Apalache directory', required=False, default='deps/apalache')
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=False, default='deps/tlapm/library')
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=False, default='deps/community/modules.jar')
parser.add_argument('--examples_root', help='Root directory of the tlaplus/examples repository', required=False, default='.')
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip parsing', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only parse models in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
parser.add_argument('--enable_assertions', help='Enable Java assertions (pass -enableassertions to JVM)', action='store_true')
args = parser.parse_args()

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
apalache_jar_path = normpath(join(args.apalache_path, 'lib', 'apalache.jar'))
tlaps_modules = normpath(args.tlapm_lib_path)
community_modules = normpath(args.community_modules_jar_path)
examples_root = args.examples_root
skip_modules = args.skip
only_modules = args.only
enable_assertions = args.enable_assertions

def parse_module(path):
    """
    Parse the given module using SANY.
    """
    logging.info(path)
    # Jar paths must go first
    jvm_parameters = [
        '-cp', pathsep.join([
            tools_jar_path,
            apalache_jar_path,
            dirname(path),
            community_modules,
            tlaps_modules
        ])
    ] + (['-enableassertions'] if enable_assertions else [])
    sany_parameters = ['-error-codes', path]
    sany = subprocess.run(
        ['java'] + jvm_parameters + ['tla2sany.SANY'] + sany_parameters,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True
    )
    output = ' '.join(sany.args) + '\n' + sany.stdout
    if 0 == sany.returncode:
        logging.debug(output)
        return True
    else:
        logging.error(output)
        return False

manifest = tla_utils.load_all_manifests(examples_root)

# List of all modules to parse and whether they should use TLAPS imports
modules = [
    tla_utils.from_cwd(examples_root, module['path'])
    for path, spec in manifest
    for module in spec['modules']
        if module['path'] not in skip_modules
        and (only_modules == [] or module['path'] in only_modules)
]

for path in skip_modules:
    logging.info(f'Skipping {path}')

# Parse specs in parallel
thread_count = cpu_count() if not args.verbose else 1
logging.info(f'Parsing using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(parse_module, modules)
    exit(0 if all(results) else 1)

