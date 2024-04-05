"""
Validate all proofs in all modules with TLAPM.
"""

from argparse import ArgumentParser
from os.path import dirname, join, normpath
import logging
import subprocess
from timeit import default_timer as timer
import tla_utils

logging.basicConfig(level=logging.INFO)

parser = ArgumentParser(description='Validate all proofs in all modules with TLAPM.')
parser.add_argument('--tlapm_path', help='Path to TLAPM install dir; should have bin and lib subdirs', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip checking', required=False, default=[])
args = parser.parse_args()

tlapm_path = normpath(args.tlapm_path)
manifest_path = normpath(args.manifest_path)
manifest = tla_utils.load_json(manifest_path)
examples_root = dirname(manifest_path)
skip_modules = [normpath(path) for path in args.skip]

proof_module_paths = [
    module['path']
    for spec in manifest['specifications']
    for module in spec['modules']
        if 'proof' in module['features']
        and normpath(module['path']) not in skip_modules
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
        ], capture_output=True
    )
    end_time = timer()
    logging.info(f'Checked proofs in {end_time - start_time:.1f}s')
    if tlapm.returncode != 0:
        logging.error(f'Proof checking failed in {module_path}:')
        logging.error(tlapm.stderr.decode('utf-8'))
        success = False

exit(0 if success else 1)

