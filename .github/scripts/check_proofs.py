"""
Validate all proofs in all modules with TLAPM.
"""

from argparse import ArgumentParser
from os.path import dirname, join, normpath
import logging
import subprocess
from timeit import default_timer as timer
import tla_utils

parser = ArgumentParser(description='Validate all proofs in all modules with TLAPM.')
parser.add_argument('--tlapm_path', help='Path to TLAPM install dir; should have bin and lib subdirs', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip checking', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only check proofs in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
args = parser.parse_args()

tlapm_path = normpath(args.tlapm_path)
manifest_path = normpath(args.manifest_path)
manifest = tla_utils.load_json(manifest_path)
examples_root = dirname(manifest_path)
skip_modules = args.skip
only_modules = args.only

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

proof_module_paths = [
    module['path']
    for spec in manifest['specifications']
    for module in spec['modules']
        if 'proof' in module['features']
        and module['path'] not in skip_modules
        and (only_modules == [] or model['path'] in only_models)
]

for path in skip_modules:
    logging.info(f'Skipping {path}')

success = True
tlapm_path = join(tlapm_path, 'bin', 'tlapm')
for module_path in proof_module_paths:
    logging.info(module_path)
    start_time = timer()
    module_path = tla_utils.from_cwd(examples_root, module_path)
    module_dir = dirname(module_path)
    tlapm = subprocess.run(
        [
            tlapm_path, module_path,
            '-I', module_dir
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True
    )
    end_time = timer()
    logging.info(f'Checked proofs in {end_time - start_time:.1f}s')
    if tlapm.returncode != 0:
        logging.error(f'Proof checking failed in {module_path}:')
        logging.error(tlapm.stdout)
        success = False
    else:
        logging.debug(tlapm.stdout)

exit(0 if success else 1)

