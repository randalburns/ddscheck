#!/bin/sh
# Certify and check every result in DDS's table for one deal, running contracts in parallel.
#
# Usage: scripts/prove_deal.sh "N:QJ6.K652.J85.T98 873.J97.AT764.Q4 K5.T83.KQ9.A7652 AT942.AQ4.32.KJ3" outdir
#
# Set SOLVER=own to get the moves from altsolve instead of DDS. JOBS sets the parallelism; altsolve
# uses about 700 MB per job.
set -eu

[ $# -eq 2 ] || { echo "usage: $0 \"<PBN deal>\" <output directory>" >&2; exit 2; }
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PBN=$1
OUT=$2
JOBS=${JOBS:-8}
mkdir -p "$OUT"

for strain in N S H D C; do
  for declarer in N E S W; do
    echo "$strain $declarer"
  done
done | PBN="$PBN" OUT="$OUT" BIN="$ROOT/build/ddscert" SOLVER="${SOLVER:-dds}" xargs -P "$JOBS" -L 1 sh -c \
  '"$BIN" --pbn "$PBN" --strain "$0" --declarer "$1" --solver "$SOLVER" -o "$OUT/$0_$1.cert" | grep -v "^wrote"'

cd "$ROOT"
.lake/build/bin/ddscheck "$OUT"/*.cert
