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

special_fields = ['pdf', 'bibtex', 'artifact']

subst = {
        '---\n': '',
        'nocite: \"\[@\*\]\"\n': '',
        r'issued: ([0-9][0-9][0-9][0-9])-([0-9][0-9])':\
                r'issued:\n  - year: \1\n    month: \2',
        'month: 0': 'month: ',
        r'\$\([0-9]\)*^{\(.*\)}\$': '\1<sup>\2</sup>',
        r'(title:.*)\[': '\1',
        r'\]{\.nocase}': '',
        r'(' + "|".join(w for w in special_fields) + ')=(.*),': r'\n  \1: \2',
        r'(' + "|".join(w for w in special_fields) + ')(.*)"': r'\1 \2',
        r'.*note: "\n': '',
        r'\s+\n': '\n',
        }

for s, r in subst.items():
    markdown = re.sub(s, r, markdown)

with path_outfile.open('w') as outfile:
    outfile.write(markdown)

