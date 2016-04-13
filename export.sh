#!/bin/bash

set -e -u -x

D="$PWD"
TEMP="$(mktemp -d)"

cd "$TEMP"
mkdir IBDD

cp -r "$D"/thy/{*.thy,document} IBDD

sed -i 's/$AFP/../' IBDD/*.thy

cat >IBDD/ROOT <<HEREFILE
session "IBDD" (AFP) = IBDDUsedAFP +
	options [document = pdf, document_output = "output"]
	theories
$(cd "$D/thy" && (find . -name \*.thy | grep -v BDDCode | sed -n 's/^\(.*\).thy$/		"\1"/p'))
	document_files
		"root.tex"

session IBDDUsedAFP (AFP) = HOL + (* Extra session without [document = pdf] so we won't inherit any errors *)
	theories[document=false]
$(sed -n 's/$AFP/../p' "$D/thy/ROOT")
HEREFILE

tar czvf IBDD.tgz IBDD/
cp IBDD.tgz "$D"

cd "$D"
rm -rf "$TEMP"
