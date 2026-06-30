#!/bin/sh
# Regenerate the Alectryon HTML for the finelt development.
#
# Unlike coqdoc (see gen-finelt-doc.sh), Alectryon re-runs every proof through
# coq-lsp to capture goals/hypotheses, so this is slow for the large files
# (raw_validity.v, adequacy.v take several minutes each).
#
# Output goes to doc/finelt-alectryon/ (one <file>.html per source file).
# Run from anywhere; paths resolve relative to this script's directory.
set -e

# Move to the domains directory (where this script lives).
cd "$(dirname "$0")"

ALECTRYON="${ALECTRYON:-alectryon}"

SRCDIR=theories/examples/finelt
OUTDIR=doc/finelt-alectryon

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

# --coq-driver coqlsp: use the coq-lsp backend (no sertop in this switch).
# -R theories Domains matches the logical mapping in _CoqProject.
"$ALECTRYON" --coq-driver coqlsp -R theories Domains \
  --output-directory "$OUTDIR" $VFILES

echo "Wrote Alectryon documentation to $OUTDIR/"
