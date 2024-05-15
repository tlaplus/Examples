"""
Generates a best-effort manifest.json file. This is done by scanning all
.tla and .cfg files in the specifications dir then attempting to sort them
into a spec/module/model hierarchy. Files are parsed to check for features
and imports. Human-written fields (title/description/source/authors for
specs, runtime/size/result for models) are either taken from any existing
manifest.json file or set as blank/unknown as appropriate.
"""

from check_manifest_features import *
import os
from os.path import basename, dirname, join, normpath, relpath, splitext
from pathlib import PureWindowsPath
import glob
import tla_utils
import tree_sitter_tlaplus
from tree_sitter import Language, Parser

def to_posix(path):
    """
    Converts paths to normalized Posix format.
    https://stackoverflow.com/q/75291812/2852699
    """
    return PureWindowsPath(normpath(path)).as_posix()

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
    return [
        path for path in glob.glob(f'{dir_path}/**/*.tla', root_dir=examples_root, recursive=True)
        if '_TTrace_' not in path
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

def generate_new_manifest(examples_root, ignored_dirs, parser, queries):
    """
    Generate new base manifest.json from files in specifications dir.
    """
    return {
        'specifications': [
            {
                'path': to_posix(spec_path),
                'title': spec_name,
                'description': '',
                'sources': [],
                'authors': [],
                'tags': [],
                'modules': [
                    {
                        'path': to_posix(tla_path),
                        'communityDependencies': sorted(list(get_community_module_imports(examples_root, parser, tla_path, queries))),
                        'tlaLanguageVersion': 2,
                        'features': sorted(list(get_module_features(examples_root, tla_path, parser, queries))),
                        'models': [
                            {
                                'path': to_posix(cfg_path),
                                'runtime': 'unknown',
                                'size': 'unknown',
                                'mode': 'exhaustive search',
                                'features': sorted(list(get_model_features(examples_root, cfg_path))),
                                'result': 'unknown'
                            }
                            for cfg_path in sorted(get_cfg_files(examples_root, tla_path))
                        ]
                    }
                    for tla_path in sorted(get_tla_files(examples_root, spec_path))
                ]
            }
            for (spec_path, spec_name) in get_spec_dirs(examples_root, ignored_dirs)
        ]
    }

# Integrate human-written info from existing manifest.json

def find_corresponding_spec(old_spec, new_manifest):
    specs = [
        spec for spec in new_manifest['specifications']
        if to_posix(spec['path']) == old_spec['path']
    ]
    return specs[0] if any(specs) else None

def integrate_spec_info(old_spec, new_spec):
    fields = ['title', 'description', 'authors', 'sources', 'tags']
    for field in fields:
        new_spec[field] = old_spec[field]

def find_corresponding_module(old_module, new_spec):
    modules = [
        module for module in new_spec['modules']
        if to_posix(module['path']) == to_posix(old_module['path'])
    ]
    return modules[0] if any(modules) else None

def integrate_module_info(old_module, new_module):
    fields = ['tlaLanguageVersion']
    for field in fields:
        new_module[field] = old_module[field]

def find_corresponding_model(old_model, new_module):
    models = [
        model for model in new_module['models']
        if to_posix(model['path']) == to_posix(old_model['path'])
    ]
    return models[0] if any(models) else None

def integrate_model_info(old_model, new_model):
    fields = ['runtime', 'size', 'mode', 'result', 'distinctStates', 'totalStates', 'stateDepth']
    for field in fields:
        if field in old_model:
            new_model[field] = old_model[field]

def integrate_old_manifest_into_new(old_manifest, new_manifest):
    for old_spec in old_manifest['specifications']:
        new_spec = find_corresponding_spec(old_spec, new_manifest)
        if new_spec is None:
            continue
        integrate_spec_info(old_spec, new_spec)
        for old_module in old_spec['modules']:
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
    parser = ArgumentParser(description='Generates a new manifest.json derived from files in the repo.')
    parser.add_argument('--manifest_path', help='Path to the current tlaplus/examples manifest.json file', default='manifest.json')
    parser.add_argument('--ci_ignore_path', help='Path to the CI ignore file', default='.ciignore')
    args = parser.parse_args()

    manifest_path = normpath(args.manifest_path)
    examples_root = dirname(manifest_path)
    ci_ignore_path = normpath(args.ci_ignore_path)
    ignored_dirs = tla_utils.get_ignored_dirs(ci_ignore_path)

    TLAPLUS_LANGUAGE = Language(tree_sitter_tlaplus.language())
    parser = Parser(TLAPLUS_LANGUAGE)
    queries = build_queries(TLAPLUS_LANGUAGE)

    old_manifest = tla_utils.load_json(manifest_path)
    new_manifest = generate_new_manifest(examples_root, ignored_dirs, parser, queries)
    integrate_old_manifest_into_new(old_manifest, new_manifest)

    tla_utils.write_json(new_manifest, manifest_path)

