#!/bin/bash

set -e -u

D="$PWD"
TEMP="$(mktemp -d)"

cd "$TEMP"
mkdir ROBDD

cp -r "$D"/thy/{*.thy,document} ROBDD

sed -i -e 's/$AFP/../' -e 's#\(export_code .*\) in Haskell .*$#\1 checking Haskell#' ROBDD/*.thy

cat >ROBDD/ROOT <<HEREFILE
chapter AFP
session "ROBDD" (AFP) = HOL +
	theories[document = false]
$(sed -n 's/$AFP/../p' "$D/thy/ROOT")
	theories
$(cd "$D/thy" && (find . -name \*.thy | grep -v BDD_Code | sed -n 's/^\(.*\).thy$/		"\1"/p'))
	theories[condition = ISABELLE_GHC]
		BDD_Code
	document_files
$(cd "$D/thy/document" && (find . | sed -n 's/^.*$/		"&"/p'))
HEREFILE

tar czf ROBDD.tgz ROBDD/
cp ROBDD.tgz "$D"

cd "$D"
rm -rf "$TEMP"
