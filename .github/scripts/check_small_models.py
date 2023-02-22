"""
Check all models marked as size "small" in the manifest with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

import logging
from timeit import default_timer as timer
import tla_utils

tlc_result = {
    0   : 'success',
    11  : 'deadlock failure',
    12  : 'safety failure',
    13  : 'liveness failure'
}

def check_model(module_path, model, expected_runtime):
    model_path = model['path']
    logging.info(model_path)
    expected_result = model['result']
    start_time = timer()
    tlc, hit_timeout = tla_utils.check_model(
        module_path,
        model_path,
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

logging.basicConfig(level=logging.INFO)

manifest = tla_utils.load_manifest()

# Ensure longest-running modules go first
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

