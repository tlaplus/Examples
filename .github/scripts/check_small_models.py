"""
Check all models with less than 30 second recorded runtime with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

from argparse import ArgumentParser
from datetime import timedelta
import logging
from os.path import dirname, normpath
from subprocess import CompletedProcess, TimeoutExpired
from timeit import default_timer as timer
import tla_utils

parser = ArgumentParser(description='Checks all small TLA+ models in the tlaplus/examples repo using TLC.')
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

logging.basicConfig(level = logging.DEBUG if args.verbose else logging.INFO)

tools_jar_path = normpath(args.tools_jar_path)
apalache_path = normpath(args.apalache_path)
tlapm_lib_path = normpath(args.tlapm_lib_path)
community_jar_path = normpath(args.community_modules_jar_path)
examples_root = args.examples_root
skip_models = args.skip
only_models = args.only
enable_assertions = args.enable_assertions

def check_model(module, model, expected_runtime):
    module_path = tla_utils.from_cwd(examples_root, module['path'])
    model_path = tla_utils.from_cwd(examples_root, model['path'])
    logging.info(model_path)
    hard_timeout_in_seconds = 60
    start_time = timer()
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
        hard_timeout_in_seconds
    )
    end_time = timer()
    match tlc_result:
        case CompletedProcess():
            output = ' '.join(tlc_result.args) + '\n' + tlc_result.stdout
            logging.info(f'{model_path} in {end_time - start_time:.1f}s vs. {expected_runtime.seconds}s expected')
            expected_result = model['result']
            actual_result = tla_utils.resolve_tlc_exit_code(tlc_result.returncode)
            if expected_result != actual_result:
                logging.error(f'Model {model_path} expected result {expected_result} but got {actual_result}')
                logging.error(output)
                return False
            if tla_utils.is_state_count_valid(model) and tla_utils.has_state_count(model):
                state_count_info = tla_utils.extract_state_count_info(tlc_result.stdout)
                if state_count_info is None:
                    logging.error("Failed to find state info in TLC output")
                    logging.error(output)
                    return False
                if not tla_utils.is_state_count_info_correct(model, *state_count_info):
                    logging.error("Recorded state count info differed from actual state counts:")
                    logging.error(f"(distinct/total/depth); expected: {tla_utils.get_state_count_info(model)}, actual: {state_count_info}")
                    logging.error(output)
                    return False
            logging.debug(output)
            return True
        case TimeoutExpired():
            args, timeout = tlc_result.args
            # stdout is a string on Windows, byte array everywhere else
            stdout = tlc_result.stdout if type(tlc_result.stdout) == str else tlc_result.stdout.decode('utf-8')
            output = ' '.join(args) + '\n' + stdout
            logging.error(f'{model_path} hit hard timeout of {timeout} seconds')
            logging.error(output)
            return False
        case _:
            logging.error(f'Unhandled TLC result type {type(tlc_result)}: {tlc_result}')
            return False

# Ensure longest-running modules go first
manifest = tla_utils.load_all_manifests(examples_root)
small_models = sorted(
    [
        (module, model, runtime)
        for path, spec in manifest
        for module in spec['modules']
        for model in module['models']
            if (runtime := tla_utils.parse_timespan(model['runtime'])) <= timedelta(seconds=30)
            and model['path'] not in skip_models
            and (only_models == [] or model['path'] in only_models)
    ],
    key = lambda m: m[2],
    reverse=True
)

for path in skip_models:
    logging.info(f'Skipping {path}')

success = all([check_model(*model) for model in small_models])
exit(0 if success else 1)

