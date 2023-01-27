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
import glob

def get_tla_files(dir):
    """
    Gets paths of all .tla files in the given directory.
    """
    return [normpath(path) for path in glob.glob(f'{dir.path}/**/*.tla', recursive=True)]

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
        normpath(path) for path in glob.glob(f'{join(parent_dir, module_name)}*.cfg')
        if splitext(basename(path))[0] not in other_module_names
    ]

# Generate new base manifest.json from files in specifications dir
new_manifest = {
    'specifications': [
        {
            'path': normpath(dir.path),
            'title': dir.name,
            'description': '',
            'source': '',
            'authors': [],
            'tags': [],
            'modules': [
                {
                    'path': tla_path,
                    'communityDependencies': sorted(list(get_community_module_imports(tla_path))),
                    'tlaLanguageVersion': 2,
                    'features': sorted(list(get_module_features(tla_path))),
                    'models': [
                        {
                            'path': cfg_path,
                            'runtime': 'unknown',
                            'size': 'unknown',
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
        ) if dir.is_dir() and any(get_tla_files(dir))
    ]
}

# Integrate human-written info from existing manifest.json

def find_corresponding_spec(old_spec, new_manifest):
    return [
        spec for spec in new_manifest['specifications']
        if normpath(spec['path']) == old_spec['path']
    ][0]

def integrate_spec_info(old_spec, new_spec):
    fields = ['title', 'description', 'source', 'tags']
    for field in fields:
        new_spec[field] = old_spec[field]
    new_spec['authors'] = sorted(old_spec['authors'])

def find_corresponding_module(old_module, new_spec):
    return [
        module for module in new_spec['modules']
        if normpath(module['path']) == normpath(old_module['path'])
    ][0]

def integrate_module_info(old_module, new_module):
    fields = ['tlaLanguageVersion']
    for field in fields:
        new_module[field] = old_module[field]

def find_corresponding_model(old_model, new_module):
    return [
        model for model in new_module['models']
        if normpath(model['path']) == normpath(old_model['path'])
    ][0]

def integrate_model_info(old_model, new_model):
    fields = ['runtime', 'size', 'result']
    for field in fields:
        new_model[field] = old_model[field]

old_manifest = None
with open('manifest.json', 'r') as old_manifest_file:
    old_manifest = json.load(old_manifest_file)

for old_spec in old_manifest['specifications']:
    new_spec = find_corresponding_spec(old_spec, new_manifest)
    integrate_spec_info(old_spec, new_spec)
    for old_module in old_spec['modules']:
        new_module = find_corresponding_module(old_module, new_spec)
        integrate_module_info(old_module, new_module)
        for old_model in old_module['models']:
            new_model = find_corresponding_model(old_model, new_module)
            integrate_model_info(old_model, new_model)

# Write generated manifest to file
with open('manifest.json', 'w') as new_manifest_file:
    json.dump(new_manifest, new_manifest_file, indent=2, ensure_ascii=False)

