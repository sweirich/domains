#!/bin/sh
# Regenerate the coqdoc HTML for the finelt development.
#
# Output goes to doc/finelt/ (index.html is the entry point).
# Run from anywhere; paths are resolved relative to this script's directory.
#
# Requires the .glob files produced by compilation, so build first if needed:
#   make -f CoqMakefile
set -e

# Move to the domains directory (where this script lives).
cd "$(dirname "$0")"

# coqdoc or its rocq alias.
DOC="${COQDOC:-coqdoc}"
command -v "$DOC" >/dev/null 2>&1 || DOC=rocqdoc

SRCDIR=theories/examples/finelt
OUTDIR=doc/finelt

FILES="
  utils
  findom
  types
  selection
  raw_semantics
  eval_substitution
  raw_validity
  typing_semantics
  adequacy
"

VFILES=""
for f in $FILES; do
  VFILES="$VFILES $SRCDIR/$f.v"
done

mkdir -p "$OUTDIR"

# -R theories Domains matches the logical mapping in _CoqProject.
"$DOC" --toc --html --utf8 -R theories Domains -d "$OUTDIR" $VFILES

echo "Wrote documentation to $OUTDIR/ (open $OUTDIR/index.html)"
