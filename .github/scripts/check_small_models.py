"""
Check all models marked as size "small" in the manifest with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

from argparse import ArgumentParser
import logging
from os.path import dirname, join, normpath
from timeit import default_timer as timer
import tla_utils

tlc_result = {
    0   : 'success',
    11  : 'deadlock failure',
    12  : 'safety failure',
    13  : 'liveness failure'
}

parser = ArgumentParser(description='Checks all small TLA+ models in the tlaplus/examples repo using TLC.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=True)
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
args = parser.parse_args()

logging.basicConfig(level=logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root_path = dirname(manifest_path)

def check_model(module_path, model, expected_runtime):
    module_path = normpath(join(examples_root_path, module_path))
    model_path = normpath(join(examples_root_path, model['path']))
    logging.info(model_path)
    expected_result = model['result']
    start_time = timer()
    tlc, hit_timeout = tla_utils.check_model(
        tools_jar_path,
        module_path,
        model_path,
        tlapm_lib_path,
        community_jar_path,
        model['mode'],
        model['config'],
        60
    )
    end_time = timer()
    if hit_timeout:
        logging.error(f'{model_path} timed out')
        return False
    logging.info(f'{model_path} in {end_time - start_time:.1f}s vs. {expected_runtime.seconds}s expected')
    actual_result = tlc_result[tlc.returncode] if tlc.returncode in tlc_result else str(tlc.returncode)
    if expected_result != actual_result:
        logging.error(f'Model {model_path} expected result {expected_result} but got {actual_result}')
        logging.error(tlc.stdout.decode('utf-8'))
        return False
    return True

# Ensure longest-running modules go first
manifest = tla_utils.load_json(manifest_path)
small_models = sorted(
    [
        (module['path'], model, tla_utils.parse_timespan(model['runtime']))
        for spec in manifest['specifications']
        for module in spec['modules']
        for model in module['models'] if model['size'] == 'small'
    ],
    key = lambda m: m[2],
    reverse=True
)

success = all([check_model(*model) for model in small_models])
exit(0 if success else 1)

