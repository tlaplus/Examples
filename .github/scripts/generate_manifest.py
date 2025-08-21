"""
Generates best-effort manifest.json files. This is done by scanning all
.tla and .cfg files in the specifications dir then attempting to sort them
into a spec/module/model hierarchy. Files are parsed to check for features
and imports. Human-written fields (title/description/source/authors for
specs, runtime & result for models) are either taken from any existing
manifest.json file or set as blank/unknown as appropriate.
"""

from check_manifest_features import *
import os
from os.path import basename, dirname, join, normpath, relpath, splitext, isfile
import glob
import tla_utils
import tree_sitter_tlaplus
from tree_sitter import Language, Parser

def get_spec_dirs(examples_root, ignored_dirs):
    """
    Get all directories under the specifications dir, sorted alphabetically.
    """
    ignore = lambda path : tla_utils.ignore(ignored_dirs, path)
    return [
        (path, name) for (path, name) in [
            (relpath(dir.path, start=examples_root), dir.name)
            for dir in sorted(os.scandir(tla_utils.from_cwd(examples_root, 'specifications')), key=lambda d: d.name)
            if dir.is_dir()
        ]
        if any(get_tla_files(examples_root, path))
        and not ignore(path)
    ]

def get_tla_files(examples_root, dir_path):
    """
    Gets paths of all .tla files in the given directory, except for error
    trace specs.
    """
    return sorted(
        path
        for path in glob.glob(f'{dir_path}/**/*.tla', root_dir=examples_root, recursive=True)
        if '_TTrace_' not in path
    )

def get_tla_file_features(examples_root, dir_path, parser, queries):
    """
    Gets paths of all .tla files in a given directory, along with their
    features.
    """
    return [
        (path, get_module_features(examples_root, path, parser, queries))
        for path in get_tla_files(examples_root, dir_path)
    ]

def get_cfg_files(examples_root, tla_path):
    """
    Assume a .cfg file in the same directory as the .tla file and with the
    same name is a model of that .tla file; also assume this of any .cfg
    files where the .tla file name is only a prefix of the .cfg file name,
    unless there are other .tla file names in the directory that are longer
    prefixes of the .cfg file name.
    """
    parent_dir = dirname(tla_path)
    module_name, _ = splitext(basename(tla_path))
    other_module_names = [other for other in get_module_names_in_dir(examples_root, parent_dir) if other != module_name]
    return [
        path
        for path in glob.glob(f'{join(parent_dir, module_name)}*.cfg', root_dir=examples_root)
        if not any([
            splitext(basename(path))[0].startswith(other_module_name)
            for other_module_name in other_module_names
            if len(other_module_name) > len(module_name)
        ])
    ]

def generate_new_manifest(examples_root, spec_path, spec_name, parser, queries):
    """
    Generate new manifest.json file for a given specification directory.
    """
    return {
        'sources': [],
        'authors': [],
        'tags': [],
        'modules': [
            {
                'path': tla_utils.to_posix(tla_path),
                'communityDependencies': sorted(list(get_community_module_imports(examples_root, parser, tla_path, queries))),
                'features': sorted(list(module_features - {'proof'})),
                'models': [
                    {
                        'path': tla_utils.to_posix(cfg_path),
                        'runtime': 'unknown',
                        'mode': 'exhaustive search',
                        'result': 'unknown'
                    }
                    for cfg_path in sorted(get_cfg_files(examples_root, tla_path))
                ]
            } | ({'proof' : {'runtime': 'unknown'}} if 'proof' in module_features else {})
            for tla_path, module_features in get_tla_file_features(examples_root, spec_path, parser, queries)
        ]
    }

# Integrate human-written info from existing manifest.json

def get_old_manifest(spec_path):
    old_manifest_path = join(spec_path, 'manifest.json')
    return tla_utils.load_json(old_manifest_path) if isfile(old_manifest_path) else None

def integrate_spec_info(old_manifest, new_spec):
    fields = ['authors', 'sources', 'tags']
    for field in fields:
        new_spec[field] = old_manifest[field]

def find_corresponding_module(old_module, new_spec):
    modules = [
        module for module in new_spec['modules']
        if tla_utils.to_posix(module['path']) == tla_utils.to_posix(old_module['path'])
    ]
    return modules[0] if any(modules) else None

def integrate_module_info(old_module, new_module):
    required_fields = []
    for field in required_fields:
        new_module[field] = old_module[field]
    optional_fields = ['proof']
    for field in optional_fields:
        if field in old_module:
            new_module[field] = old_module[field]

def find_corresponding_model(old_model, new_module):
    models = [
        model for model in new_module['models']
        if tla_utils.to_posix(model['path']) == tla_utils.to_posix(old_model['path'])
    ]
    return models[0] if any(models) else None

def integrate_model_info(old_model, new_model):
    fields = ['runtime', 'mode', 'result', 'distinctStates', 'totalStates', 'stateDepth']
    for field in fields:
        if field in old_model:
            new_model[field] = old_model[field]

def integrate_old_manifest_into_new(old_manifest, new_spec):
    if old_manifest is None:
        return
    integrate_spec_info(old_manifest, new_spec)
    for old_module in old_manifest['modules']:
        new_module = find_corresponding_module(old_module, new_spec)
        if new_module is None:
            continue
        integrate_module_info(old_module, new_module)
        for old_model in old_module['models']:
            new_model = find_corresponding_model(old_model, new_module)
            if new_model is None:
                continue
            integrate_model_info(old_model, new_model)

if __name__ == '__main__':
    parser = ArgumentParser(description='Generates new manifest.json files derived from files in the repo.')
    parser.add_argument('--ci_ignore_path', help='Path to the CI ignore file', default='.ciignore')
    args = parser.parse_args()

    ci_ignore_path = normpath(args.ci_ignore_path)
    examples_root = dirname(ci_ignore_path)
    ignored_dirs = tla_utils.get_ignored_dirs(ci_ignore_path)

    TLAPLUS_LANGUAGE = Language(tree_sitter_tlaplus.language())
    parser = Parser(TLAPLUS_LANGUAGE)
    queries = build_queries(TLAPLUS_LANGUAGE)

    for (spec_path, spec_name) in get_spec_dirs(examples_root, ignored_dirs):
        old_manifest = get_old_manifest(spec_path)
        new_manifest = generate_new_manifest(examples_root, spec_path, spec_name, parser, queries)
        integrate_old_manifest_into_new(old_manifest, new_manifest)
        tla_utils.write_json(new_manifest, join(spec_path, 'manifest.json'))

