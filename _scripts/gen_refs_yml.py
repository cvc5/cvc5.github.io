#! /bin/python

import pathlib
import re
import subprocess

parent_dir = pathlib.Path(__file__).parent.parent.resolve()
path_refs_bib = parent_dir.joinpath("_refs", "refs.bib")
path_outfile = parent_dir.joinpath("_data", "publications.yml")

pandoc_args = [
        'pandoc',
        path_refs_bib.as_posix(),
        '-s',
        '-f', 'biblatex',
        '-t', 'markdown'
        ]

markdown = subprocess.check_output(pandoc_args).decode('utf8').strip()

special_fields = ['pdf', 'slides', 'bibtex', 'artifact', 'award']

def format_note(match):
    note = re.sub(r' +', ' ', match.groups()[0].replace('\n', ' '))
    note = note.split(',')
    return ''.join('\n  ' + n.strip() for n in note)

subst = {
        '---\n': '',
        '\n---': '',
        r'\\\\\\\\\\\\\_': '_', # remove 6 \ before _
        r'\\\\\\\_': '_', # remove 3 \ before _
        'nocite: \"\[@\*\]\"\n': '',
        r'issued: ([0-9][0-9][0-9][0-9])-([0-9][0-9])':\
                r'issued:\n  - year: \1\n    month: \2',
        r'issued: ([0-9][0-9][0-9][0-9])': \
                r'issued:\n  - year: \1\n    month: 01',
        'month: 0': 'month: ',
        r'\$([0-9]*)\^\{(.*)\}\$': r'\1<sup>\2</sup>',
        r'(title:.*)\[': r'\1',
        r'\]{\.nocase}': '',
        r'.*note: "([\s\S]*?)"': format_note,
        r'\s+\n': '\n',
        }

for s, r in subst.items():
    markdown = re.sub(s, r, markdown)

with path_outfile.open('w') as outfile:
    outfile.write(markdown)

