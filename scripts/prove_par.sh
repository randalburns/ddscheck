#!/bin/sh
# Prove DDS's par score for a deal: certify the whole table, then compare the par it implies.
#
# Usage: scripts/prove_par.sh "<PBN deal>" none|both|ns|ew N|E|S|W <output directory>
set -eu

[ $# -eq 4 ] || { echo "usage: $0 \"<PBN deal>\" none|both|ns|ew N|E|S|W <output directory>" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/.." && pwd)
"$ROOT/scripts/prove_deal.sh" "$1" "$4"
SCORE=$("$ROOT/build/ddspar" --pbn "$1" --vul "$2" --dealer "$3")
echo "DDS par score: $SCORE (North-South's point of view)"
cd "$ROOT"
.lake/build/bin/ddscheck --par "$2" "$3" "$SCORE" "$4"/*.cert
