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
parser.add_argument('--readme_path', help='Path to the tlaplus/examples README.md file', required=True)
args = parser.parse_args()

readme = None
with open(normpath(args.readme_path), 'r', encoding='utf-8') as readme_file:
    readme = mistletoe.Document(readme_file)

columns = ['name', 'authors', 'beginner', 'proof', 'tlc', 'pcal', 'apalache']

def get_column(row, index):
    '''
    Gets the cell of the given column in the given row.
    '''
    return row.children[columns.index(index)].children[0]

def remove_column(table, col_index):
    '''
    Removes the column of the given index from the table.
    '''
    index = columns.index(col_index)
    table.header.children.pop(index)
    table.column_align.pop(index)
    for row in table.children:
        row.children.pop(index)

def blank_column(table, col_index):
    '''
    Removes all data in the given column.
    '''
    index = columns.index(col_index)
    for row in table.children:
        row.children[index].children = []

def swap_columns(table, first_col_index, second_col_index):
    '''
    Swaps two columns in a table.
    '''
    first = columns.index(first_col_index)
    second = columns.index(second_col_index)
    table.header.children[second], table.header.children[first] = table.header.children[first], table.header.children[second]
    table.column_align[second], table.column_align[first] = table.column_align[first], table.column_align[second]
    for row in table.children:
        row.children[second], row.children[first] = row.children[first], row.children[second]


def format_table(table):
    '''
    All table transformations should go here.
    '''
    return

table = next((child for child in readme.children if isinstance(child, Table)))
format_table(table)

# Write formatted markdown to README.md
with open(normpath(args.readme_path), 'w', encoding='utf-8') as readme_file:
    with MarkdownRenderer() as renderer:
        readme_file.write(renderer.render(readme))

