#!/bin/bash

set -e -u

D="$PWD"
TEMP="$(mktemp -d)"

cd "$TEMP"
mkdir IBDD

cp -r "$D"/thy/{*.thy,document} IBDD

sed -i -e 's/$AFP/../' -e 's#\(export_code .*\) in Haskell .*$#\1 checking Haskell#' IBDD/*.thy

cat >IBDD/ROOT <<HEREFILE
chapter AFP
session "IBDD" (AFP) = HOL +
	theories[document=false]
$(sed -n 's/$AFP/../p' "$D/thy/ROOT")
	theories
$(cd "$D/thy" && (find . -name \*.thy | sed -n 's/^\(.*\).thy$/		"\1"/p'))
	document_files
		"root.tex"
HEREFILE

tar czf IBDD.tgz IBDD/
cp IBDD.tgz "$D"

cd "$D"
rm -rf "$TEMP"
