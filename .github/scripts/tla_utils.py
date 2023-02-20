from datetime import datetime
import json
from os.path import normpath
import subprocess

def ignore(ignored_dirs, path):
    """
    Determines whether the given path is covered by paths in the .ciignore
    file and thus should be ignored.
    """
    return any([normpath(path).startswith(ignore_dir) for ignore_dir in ignored_dirs])

def is_blank(text):
    """
    Whether the given string is composed entirely of space character.
    """
    all([c.isspace() for c in text])

def get_ignored_dirs():
    """
    Parses the .ciignore file to get the set of ignored directories.
    """
    with open('.ciignore', 'r') as ignore_file:
        return set([
            normpath(line.strip())
            for line in ignore_file.readlines()
            if not line.startswith('#') and not is_blank(line)
        ])

def load_json(path):
    """
    Loads the json file at the given path.
    """
    with open(normpath(path), 'r', encoding='utf-8') as file:
        return json.load(file)

def load_manifest():
    """
    Loads the manifest.json file.
    """
    return load_json('manifest.json')

def load_schema():
    """
    Loads the schema for the manifest.json file.
    """
    return load_json('manifest-schema.json')

def parse_timespan(unparsed):
    """
    Parses the timespan format used in the manifest.json format.
    """
    pattern = '%H:%M:%S'
    return datetime.strptime(unparsed, pattern) - datetime.strptime('00:00:00', pattern)

def get_run_mode(mode):
    """
    Converts the model run mode found in manifest.json into TLC CLI
    parameters.
    """
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
    """
    Converts the model config found in manifest.json into TLC CLI
    parameters.
    """
    return ['-deadlock'] if 'ignore deadlock' in config else []

def check_model(module_path, model_path, mode, config, timeout):
    """
    Model-checks the given model against the given module.
    """
    module_path = normpath(module_path)
    model_path = normpath(model_path)
    tlaps_modules = normpath('tlapm/library')
    try:
        tlc = subprocess.run(
            [
                'java',
                '-Dtlc2.TLC.ide=Github',
                '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
                '-XX:+UseParallelGC',
                '-cp', f'tla2tools.jar:{tlaps_modules}',
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

