"""
Generates a best-effort manifest.json file. This is done by scanning all
.tla and .cfg files in the specifications dir then attempting to sort them
into a spec/module/model hierarchy. Files are parsed to check for features
and imports. Human-written fields (title/description/source/authors for
specs, runtime/size/result for models) are either taken from any existing
manifest.json file or set as blank/unknown as appropriate.
"""

from check_manifest_features import get_community_module_imports, get_module_features, get_module_names_in_dir, get_model_features
import json
import os
from os.path import basename, dirname, join, normpath, splitext
from pathlib import PureWindowsPath
import glob
import tla_utils
from tree_sitter import Language, Parser

def to_posix(path):
    """
    Converts paths to normalized Posix format.
    https://stackoverflow.com/q/75291812/2852699
    """
    return PureWindowsPath(normpath(path)).as_posix()

def get_tla_files(dir):
    """
    Gets paths of all .tla files in the given directory, except for error
    trace specs.
    """
    return [
        path for path in glob.glob(f'{dir.path}/**/*.tla', recursive=True)
        if '_TTrace_' not in path
    ]

def get_cfg_files(tla_path):
    """
    Assume a .cfg file in the same directory as the .tla file and with the
    same name is a model of that .tla file; also assume this of any .cfg
    files where the .tla file name is only a prefix of the .cfg file name,
    unless there are other .tla file names in the directory that exactly
    match the .cfg file name.
    """
    parent_dir = dirname(tla_path)
    module_name, _ = splitext(basename(tla_path))
    other_module_names = [other for other in get_module_names_in_dir(parent_dir) if other != module_name]
    return [
        path for path in glob.glob(f'{join(parent_dir, module_name)}*.cfg')
        if splitext(basename(path))[0] not in other_module_names
    ]

Language.build_library(
  'build/tree-sitter-languages.so',
  ['tree-sitter-tlaplus']
)

ignored_dirs = tla_utils.get_ignored_dirs()
ignore = lambda path : tla_utils.ignore(ignored_dirs, path)

# Generate new base manifest.json from files in specifications dir
new_manifest = {
    'specifications': [
        {
            'path': to_posix(dir.path),
            'title': dir.name,
            'description': '',
            'source': '',
            'authors': [],
            'tags': [],
            'modules': [
                {
                    'path': to_posix(tla_path),
                    'communityDependencies': sorted(list(get_community_module_imports(tla_path))),
                    'tlaLanguageVersion': 2,
                    'features': sorted(list(get_module_features(tla_path))),
                    'models': [
                        {
                            'path': to_posix(cfg_path),
                            'runtime': 'unknown',
                            'size': 'unknown',
                            'mode': 'exhaustive search',
                            'config': [],
                            'features': sorted(list(get_model_features(cfg_path))),
                            'result': 'unknown'
                        }
                        for cfg_path in sorted(get_cfg_files(tla_path))
                    ]
                }
                for tla_path in sorted(get_tla_files(dir))
            ]
        }
        for dir in sorted(
            os.scandir('specifications'), key=lambda d: d.name
        ) if dir.is_dir() and any(get_tla_files(dir)) and not ignore(dir.path)
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
    fields = ['title', 'description', 'source', 'tags']
    for field in fields:
        new_spec[field] = old_spec[field]
    new_spec['authors'] = sorted(old_spec['authors'])

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
    fields = ['runtime', 'size', 'mode', 'config', 'result']
    for field in fields:
        new_model[field] = old_model[field]

old_manifest = tla_utils.load_manifest()

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

# Write generated manifest to file
with open('manifest.json', 'w', encoding='utf-8') as new_manifest_file:
    json.dump(new_manifest, new_manifest_file, indent=2, ensure_ascii=False)

