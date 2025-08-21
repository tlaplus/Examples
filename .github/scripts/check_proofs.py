"""
Validate all proofs in all modules with TLAPM.
"""

from argparse import ArgumentParser
from datetime import timedelta
from os.path import dirname, join, normpath
import logging
import subprocess
from timeit import default_timer as timer
import tla_utils

parser = ArgumentParser(description='Validate all proofs in all modules with TLAPM.')
parser.add_argument('--tlapm_path', help='Path to TLAPM install dir; should have bin and lib subdirs', required=False, default = 'deps/tlapm')
parser.add_argument('--examples_root', help='Root directory of the tlaplus/examples repository', required=False, default='.')
parser.add_argument('--runtime_seconds_limit', help='Only run proofs with expected runtime less than this value', required=False, default=60)
parser.add_argument('--skip', nargs='+', help='Space-separated list of .tla modules to skip checking', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only check proofs in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
args = parser.parse_args()

tlapm_path = normpath(args.tlapm_path)
examples_root = args.examples_root
manifest = tla_utils.load_all_manifests(examples_root)
skip_modules = args.skip
only_modules = args.only
hard_timeout_in_seconds = args.runtime_seconds_limit * 2

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

proof_module_paths = sorted(
    [
        (manifest_dir, spec, module, runtime)
        for manifest_dir, spec in manifest
        for module in spec['modules']
        if 'proof' in module
            and (runtime := tla_utils.parse_timespan(module['proof']['runtime'])) <= timedelta(seconds = args.runtime_seconds_limit)
            and module['path'] not in skip_modules
            and (only_modules == [] or module['path'] in only_modules)
    ],
    key = lambda m : m[3]
)

for path in skip_modules:
    logging.info(f'Skipping {path}')

success = True
tlapm_path = join(tlapm_path, 'bin', 'tlapm')
for manifest_dir, spec, module, expected_runtime in proof_module_paths:
    module_path = module['path']
    logging.info(module_path)
    start_time = timer()
    full_module_path = tla_utils.from_cwd(examples_root, module_path)
    module_dir = dirname(full_module_path)
    try:
        tlapm_result = subprocess.run(
            [
                tlapm_path, full_module_path,
                '-I', module_dir,
                '--stretch', '5'
            ],
            stdout  = subprocess.PIPE,
            stderr  = subprocess.STDOUT,
            text    = True,
            timeout = hard_timeout_in_seconds
        )
        end_time = timer()
        actual_runtime = timedelta(seconds = end_time - start_time)
        output = ' '.join(tlapm_result.args) + '\n' + tlapm_result.stdout
        logging.info(f'Checked proofs in {tla_utils.format_timespan(actual_runtime)} vs. {tla_utils.format_timespan(expected_runtime)} expected')
        if tlapm_result.returncode != 0:
            logging.error(f'Proof checking failed for {module_path}:')
            logging.error(output)
            success = False
        else:
            if 'proof' not in module or module['proof']['runtime'] == 'unknown':
                module['proof'] = { 'runtime' : tla_utils.format_timespan(actual_runtime) }
                manifest_path = join(manifest_dir, 'manifest.json')
                tla_utils.write_json(spec, manifest_path)
            logging.debug(output)
    except subprocess.TimeoutExpired as tlapm_result:
        # stdout is a string on Windows, byte array everywhere else
        stdout = tlapm_result.stdout if type(tlapm_result.stdout) == str else tlapm_result.stdout.decode('utf-8')
        args, timeout = tlapm_result.args
        logging.error(f'{module_path} hit hard timeout of {timeout} seconds')
        output = ' '.join(args) + '\n' + stdout
        logging.error(output)
        success = False

exit(0 if success else 1)

