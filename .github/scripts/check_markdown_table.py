"""
Validates the spec table in README.md, ensuring it matches manifest.json.
"""

from argparse import ArgumentParser
from dataclasses import dataclass
from os.path import normpath
from typing import Any, Set
import tla_utils
import mistletoe
from mistletoe.block_token import Table

@dataclass
class TableRow:
    name        : str
    path        : str
    authors     : Set[str]
    beginner    : bool
    proof       : bool
    pcal        : bool
    tlc         : bool
    apalache    : bool
    underlying  : Any

columns = ['name', 'authors', 'beginner', 'proof', 'pcal', 'tlc', 'apalache']

def get_column(row, index):
    '''
    Gets the cell of the given column in the given row.
    '''
    return row.children[columns.index(index)].children[0]

def is_column_empty(row, index):
    '''
    Whether the given column cell is empty.
    '''
    return not any(row.children[columns.index(index)].children)

def get_link_text(link):
    '''
    Gets the text in a markdown link.
    '''
    return link.children[0].content

def from_markdown(record):
    '''
    Transforms a parsed markdown table row into a normalized form.
    '''
    return TableRow(
        get_link_text(get_column(record, 'name')),
        get_column(record, 'name').target,
        set(name.strip() for name in get_column(record, 'authors').content.split(',')),
        not is_column_empty(record, 'beginner'),
        not is_column_empty(record, 'proof'),
        not is_column_empty(record, 'pcal'),
        not is_column_empty(record, 'tlc'),
        not is_column_empty(record, 'apalache'),
        record
    )

def from_json(spec):
    '''
    Transforms JSON from the manifest into a normalized form.
    '''
    return TableRow(
        spec['title'],
        spec['path'],
        set(spec['authors']),
        'beginner' in spec['tags'],
        any([module for module in spec['modules'] if 'proof' in module['features']]),
        any([module for module in spec['modules'] if 'pluscal' in module['features']]),
        any([model for module in spec['modules'] for model in module['models'] if model['mode'] != 'symbolic']),
        any([model for module in spec['modules'] for model in module['models'] if model['mode'] == 'symbolic']),
        spec
    )

parser = ArgumentParser(description='Validates the spec table in README.md against the manifest.json.')
parser.add_argument('--manifest_path', help='Path to the tlaplus/examples manifest.json file', required=True)
parser.add_argument('--readme_path', help='Path to the tlaplus/examples README.md file', required=True)
args = parser.parse_args()

manifest = tla_utils.load_json(normpath(args.manifest_path))

readme = None
with open(normpath(args.readme_path), 'r', encoding='utf-8') as readme_file:
    readme = mistletoe.Document(readme_file)

spec_table = next((child for child in readme.children if isinstance(child, Table)))

table_specs = dict([(record.path, record) for record in [from_markdown(node) for node in spec_table.children]])
manifest_specs = dict([(record.path, record) for record in [from_json(spec) for spec in manifest['specifications']]])

# Checks that set of specs in manifest and table are equivalent
success = True
specs_not_in_table = manifest_specs.keys() - table_specs.keys()
if any(specs_not_in_table):
    success = False
    print('ERROR: specs in manifest.json missing from README.md table:\n' + '\n'.join(specs_not_in_table))
specs_not_in_manifest = table_specs.keys() - manifest_specs.keys()
if any(specs_not_in_manifest):
    success = False
    print('ERROR: specs in README.md table missing from manifest.json:\n' + '\n'.join(specs_not_in_manifest))

# Join the spec records together for comparison
specs = [
    (manifest_spec, table_specs[path])
    for (path, manifest_spec) in manifest_specs.items()
    if path in table_specs
]

# Ensure spec names are identical
different_names = [
    (manifest_spec.path, manifest_spec.name, table_spec.name)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.name != table_spec.name
]
if any(different_names):
    success = False
    print('ERROR: spec names in README.md table differ from manifest.json:')
    for path, json, md in different_names:
        print(f'Spec {path} has name {json} in manifest and {md} in README')

# Ensure spec authors are identical
different_authors = [
    (manifest_spec.path, manifest_spec.authors, table_spec.authors)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.authors != table_spec.authors
]
if any(different_authors):
    success = False
    print('ERROR: spec author(s) in README.md table differ from manifest.json:')
    for path, json, md in different_authors:
        print(f'Spec {path} has author(s) {json} in manifest.json and {md} in README.md')

# Ensure Beginner flag is correct
different_beginner_flag = [
    (manifest_spec.path, manifest_spec.beginner, table_spec.beginner)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.beginner != table_spec.beginner
]
if any(different_beginner_flag):
    success = False
    print('ERROR: Beginner flags in README.md table differ from tags in manifest.json:')
    for path, json, md in different_beginner_flag:
        print(f'Spec {path} is missing a Beginner ' + ('tag in manifest.json' if md else 'flag in README.md'))

# Ensure TLAPS proof flag is correct
different_tlaps_flag = [
    (manifest_spec.path, manifest_spec.proof, table_spec.proof)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.proof != table_spec.proof
]
if any(different_tlaps_flag):
    success = False
    print('ERROR: Proof flags in README.md table differ from features in manifest.json:')
    for path, json, md in different_tlaps_flag:
        print(f'Spec {path} ' + ('incorrectly has' if md else 'is missing') + ' a proof flag in README.md table')

# Ensure PlusCal flag is correct
different_pcal_flag = [
    (manifest_spec.path, manifest_spec.pcal, table_spec.pcal)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.pcal != table_spec.pcal
]
if any(different_pcal_flag):
    success = False
    print('ERROR: PlusCal flags in README.md table differ from features in manifest.json:')
    for path, json, md in different_pcal_flag:
        print(f'Spec {path} ' + ('incorrectly has' if md else 'is missing') + ' a PlusCal flag in README.md table')

# Ensure TLC flag is correct
different_tlc_flag = [
    (manifest_spec.path, manifest_spec.tlc, table_spec.tlc)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.tlc != table_spec.tlc
]
if any(different_tlc_flag):
    success = False
    print('ERROR: TLC Model flags in README.md table differ from model records in manifest.json:')
    for path, json, md in different_tlc_flag:
        print(f'Spec {path} ' + ('incorrectly has' if md else 'is missing') + ' a TLC Model flag in README.md table')

# Ensure Apalache flag is correct
different_apalache_flag = [
    (manifest_spec.path, manifest_spec.apalache, table_spec.apalache)
    for (manifest_spec, table_spec) in specs
    if manifest_spec.apalache != table_spec.apalache
]
if any(different_apalache_flag):
    success = False
    print('ERROR: Apalache Model flags in README.md table differ from model records in manifest.json:')
    for path, json, md in different_tlc_flag:
        print(f'Spec {path} ' + ('incorrectly has' if md else 'is missing') + ' an Apalache Model flag in README.md table')

if success:
    print('SUCCESS: manifest.json concords with README.md table')
    exit(0)
else:
    print('ERROR: differences exist between manifest.json and README.md table; see above error messages')
    exit(1)

