"""
Smoke-test all models not marked as size "small" in the manifest. This
entails running them for five seconds to ensure they can actually start
and work with the spec they're supposed to be modeling.
"""

from argparse import ArgumentParser
import logging
import os
from os.path import dirname, normpath
from subprocess import CompletedProcess, TimeoutExpired
import tla_utils

parser = ArgumentParser(description='Smoke-tests all larger TLA+ models in the tlaplus/examples repo using TLC.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=True)
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=True)
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=True)
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--skip', nargs='+', help='Space-separated list of models to skip checking', required=False, default=[])
args = parser.parse_args()

tools_jar_path = normpath(args.tools_jar_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
manifest_path = normpath(args.manifest_path)
examples_root = dirname(manifest_path)
skip_models = [normpath(path) for path in args.skip]

def check_model(module_path, model):
    module_path = tla_utils.from_cwd(examples_root, module_path)
    model_path = tla_utils.from_cwd(examples_root, model['path'])
    logging.info(model_path)
    smoke_test_timeout_in_seconds = 5
    tlc_result = tla_utils.check_model(
        tools_jar_path,
        module_path,
        model_path,
        tlapm_lib_path,
        community_jar_path,
        model['mode'],
        smoke_test_timeout_in_seconds
    )
    match tlc_result:
        case TimeoutExpired():
            return True
        case CompletedProcess():
            logging.warning(f'Model {model_path} finished quickly, within {smoke_test_timeout_in_seconds} seconds; consider labeling it a small model')
            expected_result = model['result']
            actual_result = tla_utils.resolve_tlc_exit_code(tlc_result.returncode)
            if expected_result != actual_result:
                logging.error(f'Model {model_path} expected result {expected_result} but got {actual_result}')
                logging.error(tlc_result.stdout)
                return False
            return True
        case _:
            logging.error(f'Unhandled TLC result type {type(tlc_result)}: {tlc_result}')
            return False

logging.basicConfig(level=logging.INFO)

manifest = tla_utils.load_json(manifest_path)

large_models = [
    (module['path'], model)
    for spec in manifest['specifications']
    for module in spec['modules']
    for model in module['models']
        if model['size'] != 'small'
        and normpath(model['path']) not in skip_models
]

for path in skip_models:
    logging.info(f'Skipping {path}')

success = all([check_model(*model) for model in large_models])
exit(0 if success else 1)

