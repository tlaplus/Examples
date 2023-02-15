import json
from os.path import normpath
import subprocess

def ignore(ignored_dirs, path):
    return any([normpath(path).startswith(ignore_dir) for ignore_dir in ignored_dirs])

def is_blank(text):
    all([c.isspace() for c in text])

def get_ignored_dirs():
    with open('.ciignore', 'r') as ignore_file:
        return set([
            normpath(line.strip())
            for line in ignore_file.readlines()
            if not line.startswith('#') and not is_blank(line)
        ])

def load_json(path):
    with open(normpath(path), 'r', encoding='utf-8') as file:
        return json.load(file)

def load_manifest():
    return load_json('manifest.json')

def load_schema():
    return load_json('manifest-schema.json')

def get_run_mode(mode):
    if type(mode) is dict:
        if 'simulate' in mode:
            trace_count = mode['simulate']['traceCount']
            return ['-simulate', f'num={trace_count}']
        else:
            raise NotImplementedError(f'Undefined model-check mode {mode}')
    elif 'generate' == mode:
        return ['-generate']
    elif 'exhaustive search' == mode:
        return []
    else:
        raise NotImplementedError(f'Undefined model-check mode {mode}')

def get_config(config):
    return ['-deadlock'] if 'ignore deadlock' in config else []

def check_model(jar_path, module_path, model_path, mode, config, timeout):
    jar_path = normpath(jar_path)
    module_path = normpath(module_path)
    model_path = normpath(model_path)
    try:
        tlc = subprocess.run(
            [
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
            ] + get_config(config) + get_run_mode(mode),
            capture_output=True,
            timeout=timeout
        )
        return (tlc, False)
    except subprocess.TimeoutExpired:
        return (None, True)

