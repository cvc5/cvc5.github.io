#! /bin/sh
pandoc _refs/refs.bib -s -f biblatex -t markdown \
  | sed 's/^nocite: "\[@\*\]"//' \
  | sed 's/^---//' \
  | sed 's/issued: \([0-9][0-9][0-9][0-9]\)-\([0-9][0-9]\)/issued:\n  - year: \1\n    month: \2/g' \
  | sed 's/issued: \([0-9][0-9][0-9][0-9]\)/issued:\n  - year: \1\n    month: 01/g' \
  | sed 's/month: 0/month: /' \
  | sed 's/\$\([0-9]\)*^{\(.*\)}\$/\1<sup>\2<\/sup>/' \
  | sed 's/\(title:.*\)\[/\1/g' \
  | sed 's/\]{\.nocase}//g' \
  > _data/publications.yaml
sed -i 's/\(pdf\|bibtex\|artifact\)=\(.*\),/\n  \1: \2/g' _data/publications.yaml
sed -i 's/\(pdf\|bibtex\|artifact\)\(.*\)"/\1 \2/g' _data/publications.yaml
sed -i '/.*note: "/d' _data/publications.yaml
sed -i '/^\s\+$/d' _data/publications.yaml
