from datetime import datetime
import json
from os.path import join, normpath, pathsep
import subprocess
import re

def from_cwd(root, path):
    """
    Given the path from the current working directory (cwd) to a root
    directory, and a path from that root directory to some file, derives
    the path from the cwd to that file.
    """
    return normpath(join(root, normpath(path)))

def ignore(ignored_dirs, path):
    """
    Determines whether the given path is covered by paths in the .ciignore
    file and thus should be ignored.
    """
    return any([normpath(path).startswith(ignore_dir) for ignore_dir in ignored_dirs])

def is_blank(text):
    """
    Whether the given string is composed entirely of space characters.
    """
    all([c.isspace() for c in text])

def get_ignored_dirs(ci_ignore_path):
    """
    Parses the .ciignore file to get the set of ignored directories.
    """
    with open(ci_ignore_path, 'r') as ignore_file:
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

def write_json(data, path):
    """
    Writes the given json to the given file.
    """
    with open(path, 'w', encoding='utf-8') as file:
        json.dump(data, file, indent=2, ensure_ascii=False)

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

def check_model(tools_jar_path, module_path, model_path, tlapm_lib_path, community_jar_path, mode, hard_timeout_in_seconds):
    """
    Model-checks the given model against the given module.
    """
    tools_jar_path = normpath(tools_jar_path)
    module_path = normpath(module_path)
    model_path = normpath(model_path)
    tlapm_lib_path = normpath(tlapm_lib_path)
    community_jar_path = normpath(community_jar_path)
    try:
        tlc = subprocess.run(
            [
                'java',
                '-Dtlc2.TLC.ide=Github',
                '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
                '-XX:+UseParallelGC',
                # Jar paths must go first
                '-cp', pathsep.join([tools_jar_path, community_jar_path, tlapm_lib_path]),
                'tlc2.TLC',
                module_path,
                '-config', model_path,
                '-workers', 'auto',
                '-lncheck', 'final',
                '-cleanup'
            ] + get_run_mode(mode),
            timeout=hard_timeout_in_seconds,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True
        )
        return tlc
    except subprocess.TimeoutExpired as e:
        return e

def resolve_tlc_exit_code(code):
    """
    Resolves TLC's exit code to a standardized human-readable form.
    Returns the stringified exit code number if unknown.
    """
    tlc_exit_codes = {
        0   : 'success',
        10  : 'assumption failure',
        11  : 'deadlock failure',
        12  : 'safety failure',
        13  : 'liveness failure'
    }

    return tlc_exit_codes[code] if code in tlc_exit_codes else str(code)

state_count_regex = re.compile(r'(?P<total_states>\d+) states generated, (?P<distinct_states>\d+) distinct states found, 0 states left on queue.')
state_depth_regex = re.compile(r'The depth of the complete state graph search is (?P<state_depth>\d+).')

def extract_state_info(tlc_output):
    state_count_findings = state_count_regex.search(tlc_output)
    state_depth_findings = state_depth_regex.search(tlc_output)
    if state_count_findings is None or state_depth_findings is None:
        return None
    distinct_states = int(state_count_findings.group('distinct_states'))
    total_states = int(state_count_findings.group('total_states'))
    state_depth = int(state_depth_findings.group('state_depth'))
    return (distinct_states, total_states, state_depth)

