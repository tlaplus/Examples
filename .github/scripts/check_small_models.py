"""
Check all models marked as size "small" in the manifest with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

from datetime import datetime
import json
import logging
from timeit import default_timer as timer
import tla_utils

def parse_timespan(unparsed):
    pattern = '%H:%M:%S'
    return datetime.strptime(unparsed, pattern) - datetime.strptime('00:00:00', pattern)

def is_simulate_config(config):
    sim_options = [
        option for option in config
        if type(option) is dict
        and 'simulate' in option
    ]
    if any(sim_options):
        return (True, sim_options[0]['simulate']['traceCount'])
    else:
        return (False, 0)

tlc_result = {
    0   : 'success',
    11  : 'deadlock failure',
    12  : 'safety failure',
    13  : 'liveness failure'
}

def check_model(module_path, model_path, expected_result, expected_runtime, config):
    start_time = timer()
    tlc, hit_timeout = tla_utils.check_model('tla2tools.jar', module_path, model_path, config, 60)
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

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

# Ensure longest-running modules go first
small_models = sorted(
    [
        (module['path'], model['path'], model['result'], parse_timespan(model['runtime']), model['config'])
        for spec in manifest['specifications']
        for module in spec['modules']
        for model in module['models'] if model['size'] == 'small'
    ],
    key = lambda m: m[3],
    reverse=True
)

success = all([check_model(*model) for model in small_models])
exit(0 if success else 1)

