"""
Check all models marked as size "small" in the manifest with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

from concurrent.futures import ThreadPoolExecutor
import json
import logging
from os import cpu_count
import subprocess
from timeit import default_timer as timer

tlc_result = {
    0   : 'success',
    1   : 'stuttering failure',
    11  : 'deadlock failure',
    12  : 'safety failure',
    13  : 'liveness failure'
}

def check_model(model_tuple):
    start_time = timer()
    module_path, model_path, expected_result = model_tuple
    tlc = subprocess.run([
        'java',
        '-Dtlc2.TLC.stopAfter=60',
        '-Dtlc2.TLC.ide=Github',
        '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
        '-XX:+UseParallelGC',
        '-cp', 'tla2tools.jar',
        'tlc2.TLC',
        '-workers', '1',
        '-lncheck', 'final',
        '-tool',
        '-config', model_path,
        module_path
    ], capture_output=True)
    end_time = timer()
    logging.info(f'{model_path} in {end_time - start_time:.1f}s')
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

small_models = [
    (module['path'], model['path'], model['result'])
    for spec in manifest['specifications']
    for module in spec['modules']
    for model in module['models'] if model['size'] == 'small'
]

# Since these models are small we parallelize by checking multiple files at
# once instead of parallelizing state computation and exploration for each
# individual model.
thread_count = cpu_count()
logging.info(f'Checking models using {thread_count} threads')
with ThreadPoolExecutor(thread_count) as executor:
    results = executor.map(check_model, small_models)
    exit(0 if all(results) else 1)

