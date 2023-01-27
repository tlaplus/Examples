"""
Check all models marked as size "small" in the manifest with TLC. Small
models should finish executing in less than ten seconds on the GitHub CI
machines.
"""

import json
from os import cpu_count
import subprocess

manifest = None
with open('manifest.json', 'rt') as manifest_file:
    manifest = json.load(manifest_file)

small_models = [
    (module['path'], model['path'], model['result'])
    for spec in manifest['specifications']
    for module in spec['modules']
    for model in module['models'] if model['size'] == 'small'
]

for module_path, model_path, expected_result in small_models:
    print(model_path)
    tlc = subprocess.run([
        'java',
        '-Dtlc2.TLC.ide=Github',
        '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
        '-XX:+UseParallelGC',
        '-cp', 'tla2tools.jar',
        'tlc2.TLC',
        '-workers', str(cpu_count()),
        '-lncheck', 'final',
        '-tool',
        '-config', model_path,
        module_path
    ], capture_output=True)
    tlc_output = tlc.stdout.decode('utf-8')

    print(tlc_output)
    print(tlc.returncode)


