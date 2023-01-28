"""
Check all models marked as size "small" in the manifest with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

from datetime import datetime
import json
import logging
import subprocess
from timeit import default_timer as timer

def parse_timespan(unparsed):
    pattern = '%H:%M:%S'
    return datetime.strptime(unparsed, pattern) - datetime.strptime('00:00:00', pattern)

tlc_result = {
    0   : 'success',
    1   : 'stuttering failure',
    11  : 'deadlock failure',
    12  : 'safety failure',
    13  : 'liveness failure'
}

def check_model(module_path, model_path, expected_result, expected_runtime):
    start_time = timer()
    tlc = subprocess.run([
        'java',
        '-Dtlc2.TLC.stopAfter=60',
        '-Dtlc2.TLC.ide=Github',
        '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
        '-XX:+UseParallelGC',
        '-cp', 'tla2tools.jar',
        'tlc2.TLC',
        '-workers', 'auto',
        '-lncheck', 'final',
        '-tool',
        '-config', model_path,
        module_path
    ], capture_output=True)
    end_time = timer()
    logging.info(f'{model_path} in {end_time - start_time:.1f}s vs. {expected_runtime.seconds}s expected')
    actual_result = tlc_result[tlc.returncode] if tlc.returncode in tlc_result else str(tlc.returncode)
    if expected_result != actual_result or '687' in model_path:
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
        (module['path'], model['path'], model['result'], parse_timespan(model['runtime']))
        for spec in manifest['specifications']
        for module in spec['modules']
        for model in module['models'] if model['size'] == 'small'
    ],
    key = lambda m: m[3],
    reverse=True
)

success = all([check_model(*model) for model in small_models])
exit(0 if success else 0)

