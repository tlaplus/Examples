"""
Format or modify the spec table in README.md. This is a utility script kept
around for occasional modifications to the README.md table(s), such as
swapping/deleting columns or transforming each row element. By doing a simple
round-trip without any transformation the tables will also be formatted
nicely.
"""

from argparse import ArgumentParser
from os.path import normpath
import mistletoe
from mistletoe.block_token import Table
from mistletoe.markdown_renderer import MarkdownRenderer

parser = ArgumentParser(description='Formats or modifies the spec table in README.md.')
parser.add_argument('--readme_path', help='Path to the tlaplus/examples README.md file', required=False, default='README.md')
args = parser.parse_args()

columns = ['name', 'authors', 'beginner', 'proof', 'tlc', 'pcal', 'apalache']

def get_column(row, col_name):
    '''
    Gets the cell of the given column in the given row.
    '''
    return row.children[columns.index(col_name)].children[0]

def remove_column(table, col_name):
    '''
    Removes the column of the given index from the table.
    '''
    index = columns.index(col_name)
    table.header.children.pop(index)
    table.column_align.pop(index)
    for row in table.children:
        row.children.pop(index)

def blank_column(table, col_name):
    '''
    Removes all data in the given column.
    '''
    index = columns.index(col_name)
    for row in table.children:
        row.children[index].children = []

def duplicate_column(table, col_name):
    '''
    Duplicates the given column.
    '''
    index = columns.index(col_name)
    table.header.children.insert(index, table.header.children[index])
    table.column_align.insert(index, table.column_align[index])
    for row in table.children:
        row.children.insert(index, row.children[index])

def swap_columns(table, first_col_name, second_col_name):
    '''
    Swaps two columns in a table.
    '''
    first = columns.index(first_col_name)
    second = columns.index(second_col_name)
    table.header.children[second], table.header.children[first] = table.header.children[first], table.header.children[second]
    table.column_align[second], table.column_align[first] = table.column_align[first], table.column_align[second]
    for row in table.children:
        row.children[second], row.children[first] = row.children[first], row.children[second]

def format_table(table):
    '''
    All table transformations should go here.
    '''
    return

def format_document(document):
    '''
    All document transformations should go here.
    '''
    # Gets table of local specs
    local_table, remote_table = [child for child in document.children if isinstance(child, Table)]
    #format_table(local_table)
    #format_table(remote_table)

# Read, format, write
# Need to both parse & render within same MarkdownRenderer context to preserve other formatting
with MarkdownRenderer() as renderer:
    readme = None
    with open(normpath(args.readme_path), 'r', encoding='utf-8') as readme_file:
        readme = mistletoe.Document(readme_file)
    format_document(readme)
    with open(normpath(args.readme_path), 'w', encoding='utf-8') as readme_file:
        readme_file.write(renderer.render(readme))

