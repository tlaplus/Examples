import json
import subprocess

def load_json(path):
    with open(path, 'r', encoding='utf8') as file:
        return json.load(file)

def load_manifest():
    return load_json('manifest.json')

def load_schema():
    return load_json('manifest-schema.json')

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

def check_model(jar_path, module_path, model_path, config, timeout):
    is_simulate, trace_count = is_simulate_config(config)
    try:
        tlc = subprocess.run([
                'java',
                '-Dtlc2.TLC.ide=Github',
                '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
                '-XX:+UseParallelGC',
                '-cp', jar_path,
                'tlc2.TLC',
                module_path,
                '-config', model_path,
                '-workers', 'auto',
                '-lncheck', 'final',
                '-cleanup'
            ] + (['-deadlock'] if 'ignore deadlock' in config else [])
            + (['-generate'] if 'generate' in config else [])
            + (['-simulate', f'num={trace_count}'] if is_simulate else []),
            capture_output=True,
            timeout=timeout
        )
        return (tlc, False)
    except subprocess.TimeoutExpired:
        return (None, True)

