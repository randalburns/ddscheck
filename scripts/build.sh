#!/bin/sh
# Build everything: DDS, ddfast (if it builds here), the certificate generator, and the Lean checker.
# REQUIRE_DDFAST=1 makes a failed ddfast build an error.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
if [ -z "${CXX:-}" ]; then
  CXX=clang++
  # Some machines' clang picks a GCC without C++ headers unless told otherwise.
  for d in /usr/lib/gcc/x86_64-linux-gnu/14 /usr/lib/gcc/x86_64-linux-gnu/13; do
    if [ -d "$d" ] && [ -d "/usr/include/c++/$(basename "$d")" ]; then
      CXX="clang++ --gcc-install-dir=$d"
      break
    fi
  done
fi
export CXX
scripts/build_dds.sh

# ddfast (third_party/ddfast, with its extern/dds submodule, which its build script requires),
# built by its own script: AVX-512 code where the CPU has it, Google Highway's elsewhere (see
# ddfast's README; on a CPU without AVX-512 it needs Highway's headers, else ddscert is built
# without ddfast). Its endgame tables are built on first use, in $DDFAST_TABLES (default
# third_party/ddfast/build/tables).
DDFAST=third_party/ddfast
FAST_FLAGS=""
FAST_LIBS=""
if [ -f "$DDFAST/scripts/build.sh" ] && OUT="$ROOT/build/ddfast" LIBONLY=1 sh "$DDFAST/scripts/build.sh"; then
  FAST_FLAGS="-DWITH_DDFAST -I$DDFAST/include"
  FAST_LIBS="build/ddfast/libddfast.a -pthread"
  echo "built build/ddfast/libddfast.a"
else
  echo "ddfast not built (see the messages above); ddscert is built without it"
  [ "${REQUIRE_DDFAST:-0}" = 1 ] && { echo "REQUIRE_DDFAST=1: stopping" >&2; exit 1; }
fi

# shellcheck disable=SC2086
$CXX -std=c++20 -O2 -Ithird_party/dds/library/src -Itools $FAST_FLAGS tools/ddscert.cpp build/dds/libdds.a $FAST_LIBS -o build/ddscert
$CXX -std=c++20 -O2 -Ithird_party/dds/library/src tools/ddspar.cpp build/dds/libdds.a -o build/ddspar
lake build
