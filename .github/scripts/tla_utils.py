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

def parse_module(examples_root, parser, path):
    """
    Parses a .tla file with tree-sitter; returns the parse tree along with
    whether a parse error was detected.
    """
    module_text = None
    path = from_cwd(examples_root, path)
    with open(path, 'rb') as module_file:
        module_text = module_file.read()
    tree = parser.parse(module_text)
    return (tree, module_text, tree.root_node.has_error)

def all_nodes_of(query_map):
    """
    Flatten a query result to get all matched nodes. Returned in order of
    occurrence in file.
    """
    return sorted([
        node
        for capture in query_map.values()
        for node in capture
    ], key=lambda node: node.start_byte)

def node_to_string(module_bytes, node):
    """
    Gets the string covered by the given tree-sitter parse tree node.
    """
    return module_bytes[node.start_byte:node.end_byte].decode('utf-8')

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

def get_tlc_feature_flags(module_features, model_features):
    """
    Selectively enables experimental TLC features according to needs.
    """
    jvm_parameters = []
    if 'action composition' in module_features:
        jvm_parameters.append('-Dtlc2.tool.impl.Tool.cdot=true')
    return jvm_parameters

def check_model(
        tools_jar_path,
        apalache_path,
        module_path,
        model_path,
        tlapm_lib_path,
        community_jar_path,
        mode,
        module_features,
        model_features,
        enable_assertions,
        hard_timeout_in_seconds
    ):
    """
    Model-checks the given model against the given module.
    """
    tools_jar_path = normpath(tools_jar_path)
    apalache_path = normpath(join(apalache_path, 'bin', 'apalache-mc'))
    apalache_jar_path = normpath(join(apalache_path, 'lib', 'apalache.jar'))
    module_path = normpath(module_path)
    model_path = normpath(model_path)
    tlapm_lib_path = normpath(tlapm_lib_path)
    community_jar_path = normpath(community_jar_path)
    try:
        if mode == 'symbolic':
            apalache = subprocess.run([
                    apalache_path, 'check',
                    f'--config={model_path}',
                    module_path
                ],
                timeout=hard_timeout_in_seconds,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True
            )
            return apalache
        else:
            jvm_parameters = (['-enableassertions'] if enable_assertions else []) + [
                '-Dtlc2.TLC.ide=Github',
                '-Dutil.ExecutionStatisticsCollector.id=abcdef60f238424fa70d124d0c77ffff',
                '-XX:+UseParallelGC',
                # Jar paths must go first
                '-cp', pathsep.join([
                    tools_jar_path,
                    apalache_jar_path,
                    community_jar_path,
                    tlapm_lib_path
                ]),
            ] + get_tlc_feature_flags(module_features, model_features)
            tlc_parameters = [
                module_path,
                '-config', model_path,
                '-workers', 'auto',
                '-lncheck', 'final',
                '-cleanup'
            ] + get_run_mode(mode)
            tlc = subprocess.run(
                ['java'] + jvm_parameters + ['tlc2.TLC'] + tlc_parameters,
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

def is_state_count_valid(model):
    """
    Whether state count info could be valid for the given model.
    """
    return model['mode'] == 'exhaustive search' and model['result'] == 'success'

def has_state_count(model):
    """
    Whether the given model has state count info.
    """
    return 'distinctStates' in model or 'totalStates' in model or 'stateDepth' in model

def get_state_count_info(model):
    """
    Gets whatever state count info is present in the given model.
    """
    get_or_none = lambda key: model[key] if key in model else None
    return (get_or_none('distinctStates'), get_or_none('totalStates'), get_or_none('stateDepth'))

def is_state_count_info_correct(model, distinct_states, total_states, state_depth):
    """
    Whether the given state count info concords with the model.
    """
    expected_distinct_states, expected_total_states, expected_state_depth = get_state_count_info(model)
    none_or_equal = lambda expected, actual: expected is None or expected == actual
    # State depth not yet deterministic due to TLC bug: https://github.com/tlaplus/tlaplus/issues/883
    return none_or_equal(expected_distinct_states, distinct_states) and none_or_equal(expected_total_states, total_states) #and none_or_equal(expected_state_depth, state_depth)

state_count_regex = re.compile(r'(?P<total_states>\d+) states generated, (?P<distinct_states>\d+) distinct states found, 0 states left on queue.')
state_depth_regex = re.compile(r'The depth of the complete state graph search is (?P<state_depth>\d+).')

def extract_state_count_info(tlc_output):
    """
    Parse & extract state count info from TLC output.
    """
    state_count_findings = state_count_regex.search(tlc_output)
    state_depth_findings = state_depth_regex.search(tlc_output)
    if state_count_findings is None or state_depth_findings is None:
        return None
    distinct_states = int(state_count_findings.group('distinct_states'))
    total_states = int(state_count_findings.group('total_states'))
    state_depth = int(state_depth_findings.group('state_depth'))
    return (distinct_states, total_states, state_depth)

