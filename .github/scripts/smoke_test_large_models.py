"""
Smoke-test all models with runtime greater than thirty seconds. This
entails running them for five seconds to ensure they can actually start
and work with the spec they're supposed to be modeling.
"""

from argparse import ArgumentParser
from datetime import timedelta
import logging
import os
from os.path import dirname, normpath
from subprocess import CompletedProcess, TimeoutExpired
import tla_utils

parser = ArgumentParser(description='Smoke-tests all larger TLA+ models in the tlaplus/examples repo using TLC.')
parser.add_argument('--tools_jar_path', help='Path to the tla2tools.jar file', required=False, default='deps/tools/tla2tools.jar')
parser.add_argument('--apalache_path', help='Path to the Apalache directory', required=False, default='deps/apalache')
parser.add_argument('--tlapm_lib_path', help='Path to the TLA+ proof manager module directory; .tla files should be in this directory', required=False, default='deps/tlapm/library')
parser.add_argument('--community_modules_jar_path', help='Path to the CommunityModules-deps.jar file', required=False, default='deps/community/modules.jar')
parser.add_argument('--examples_root', help='Root directory of the tlaplus/examples repository', required=False, default='.')
parser.add_argument('--skip', nargs='+', help='Space-separated list of models to skip checking', required=False, default=[])
parser.add_argument('--only', nargs='+', help='If provided, only check models in this space-separated list', required=False, default=[])
parser.add_argument('--verbose', help='Set logging output level to debug', action='store_true')
parser.add_argument('--enable_assertions', help='Enable Java assertions (pass -enableassertions to JVM)', action='store_true')
args = parser.parse_args()

tools_jar_path = normpath(args.tools_jar_path)
apalache_path = normpath(args.apalache_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
examples_root = args.examples_root
skip_models = args.skip
only_models = args.only
enable_assertions = args.enable_assertions

def check_model(module, model):
    module_path = tla_utils.from_cwd(examples_root, module['path'])
    model_path = tla_utils.from_cwd(examples_root, model['path'])
    logging.info(model_path)
    smoke_test_timeout_in_seconds = 5
    tlc_result = tla_utils.check_model(
        tools_jar_path,
        apalache_path,
        module_path,
        model_path,
        tlapm_lib_path,
        community_jar_path,
        model['mode'],
        module['features'],
        enable_assertions,
        smoke_test_timeout_in_seconds
    )
    match tlc_result:
        case TimeoutExpired():
            args, _ = tlc_result.args
            logging.debug(' '.join(args))
            logging.debug(
                # Returns string on Windows, bytes everywhere else
                tlc_result.stdout
                if type(tlc_result.stdout) == str
                else tlc_result.stdout.decode('utf-8')
            )
            return True
        case CompletedProcess():
            output = ' '.join(tlc_result.args) + '\n' + tlc_result.stdout
            logging.warning(f'Model {model_path} finished quickly, within {smoke_test_timeout_in_seconds} seconds; consider updating recorded runtime')
            expected_result = model['result']
            actual_result = tla_utils.resolve_tlc_exit_code(tlc_result.returncode)
            if expected_result == actual_result:
                logging.debug(output)
            else:
                logging.error(f'Model {model_path} expected result {expected_result} but got {actual_result}')
                logging.error(output)
                return False
            return True
        case _:
            logging.error(f'Unhandled TLC result type {type(tlc_result)}: {tlc_result}')
            return False

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

manifest = tla_utils.load_all_manifests(examples_root)

large_models = [
    (module, model)
    for path, spec in manifest
    for module in spec['modules']
    for model in module['models']
        if tla_utils.parse_timespan(model['runtime']) > timedelta(seconds=30)
        and model['path'] not in skip_models
        and (only_models == [] or model['path'] in only_models)
]

for path in skip_models:
    logging.info(f'Skipping {path}')

success = all([check_model(*model) for model in large_models])
exit(0 if success else 1)

