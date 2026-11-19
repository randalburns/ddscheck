#!/bin/sh
# Continuous integration (.github/workflows/ci.yml): builds everything (scripts/build.sh), then
# runs one of two test sets, each a few minutes on one runner:
#   sh scripts/ci.sh dds      DDS against independent solvers (tests/dds_stress.cpp), the Lean
#                             rules and par evaluator against DDS (SpecVsDds, ParVsDds), the
#                             kernel-checked examples, and one certificate with DDS's moves
#   sh scripts/ci.sh ddfast   all 20 results of a deal certified with ddfast's moves (ddfast's
#                             table must agree with DDS's), one with altsolve's (likewise), every
#                             certificate checked, and tamper tests
# Needs Lean (lake) on PATH; ddfast's tables are built on first use in $DDFAST_TABLES.
# Set SKIP_BUILD=1 to test an existing build.
set -eu
cd "$(dirname "$0")/.."
MODE=${1:-}
case "$MODE" in dds|ddfast) ;; *) echo "usage: sh scripts/ci.sh dds|ddfast" >&2; exit 2 ;; esac
[ "${SKIP_BUILD:-0}" = 1 ] || REQUIRE_DDFAST=1 sh scripts/build.sh
CXX=${CXX:-clang++}
if [ "$CXX" = clang++ ]; then
  for d in /usr/lib/gcc/x86_64-linux-gnu/14 /usr/lib/gcc/x86_64-linux-gnu/13; do
    if [ -d "$d" ] && [ -d "/usr/include/c++/$(basename "$d")" ]; then CXX="clang++ --gcc-install-dir=$d"; break; fi
  done
fi
DEAL="N:QJ6.K652.J85.T98 873.J97.AT764.Q4 K5.T83.KQ9.A7652 AT942.AQ4.32.KJ3"
mkdir -p build/ci
step() { echo; echo "== $*"; }

# ddscert, failing if its solver's table disagrees with DDS's (ddscert reports it and goes on).
cert() {
  out=$(build/ddscert --pbn "$DEAL" "$@")
  echo "$out" | tail -3
  if echo "$out" | grep -q DISAGREE; then echo "$out" | grep DISAGREE; echo "FAIL: the solver disagrees with DDS"; exit 1; fi
}

if [ "$MODE" = dds ]; then
  # shellcheck disable=SC2086
  {
    $CXX -std=c++20 -O2 -Ithird_party/dds/library/src tests/dds_stress.cpp build/dds/libdds.a -o build/ci/dds_stress
    $CXX -std=c++20 -O2 -Ithird_party/dds/library/src tests/spec_vs_dds.cpp build/dds/libdds.a -o build/ci/spec_vs_dds
    $CXX -std=c++20 -O2 -Ithird_party/dds/library/src tests/par_vs_dds.cpp build/dds/libdds.a -o build/ci/par_vs_dds
  }
  step "DDS against brute force and altsolve, up to 6 tricks"
  build/ci/dds_stress 30 1 6 both
  step "DDS against altsolve, 7 to 10 tricks"
  build/ci/dds_stress 30 1 10 smart 7
  step "The Lean rules against DDS on random endgames"
  build/ci/spec_vs_dds 300 > build/ci/endgames.txt
  lake build specvsdds
  .lake/build/bin/specvsdds build/ci/endgames.txt
  step "The Lean par evaluator against DDS, on real and altered tables"
  build/ci/par_vs_dds 30 50 1 > build/ci/par_cases.txt
  lake build parvsdds
  .lake/build/bin/parvsdds build/ci/par_cases.txt
  step "Kernel-checked examples"
  lake env lean tests/RulesExamples.lean
  lake env lean tests/ParExamples.lean
  step "A certificate with DDS's moves (spades, North declares), checked"
  cert --strain S --declarer N --solver dds -o build/ci/dds_S_N.cert
  .lake/build/bin/ddscheck build/ci/dds_S_N.cert
else
  step "All 20 results certified with ddfast's moves (its table against DDS's)"
  cert --solver ddfast -o build/ci/ddfast_all.cert
  step "Checking the 20 certificates"
  .lake/build/bin/ddscheck build/ci/ddfast_all.cert
  step "A certificate with altsolve's moves (spades, North declares; its value against DDS's), checked"
  cert --strain S --declarer N --solver own -o build/ci/own_S_N.cert
  .lake/build/bin/ddscheck build/ci/own_S_N.cert
  step "Tamper tests: false claims and corrupted certificates must not be proved"
  cert --strain S --declarer N --solver ddfast -o build/ci/ddfast_S_N.cert
  python3 tests/tamper.py build/ci/ddfast_S_N.cert 6
fi
echo
echo "ci.sh $MODE: all passed"
