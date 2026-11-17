#!/bin/sh
# Build everything: DDS, ddfast (if the CPU can run it), the certificate generator, and the Lean checker.
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

# ddfast (third_party/ddfast, which contains ddclaim's tables in extern/ddclaim) needs x86-64
# with AVX-512 and BMI2, and Linux; its DDS submodule is not needed. Without them ddscert is
# built without it.
DDFAST=third_party/ddfast
FAST_FLAGS=""
FAST_LIBS=""
if [ -f "$DDFAST/src/solver.cpp" ] && [ -f "$DDFAST/extern/ddclaim/src/ddclaim.cpp" ] &&
   grep -q avx512f /proc/cpuinfo 2>/dev/null && grep -q bmi2 /proc/cpuinfo 2>/dev/null; then
  mkdir -p build/ddfast
  FAST="-std=c++20 -O3 -DNDEBUG -march=native -I$DDFAST/include -I$DDFAST/extern/ddclaim/include"
  # shellcheck disable=SC2086
  {
    $CXX $FAST -c "$DDFAST/extern/ddclaim/src/ddclaim.cpp" -o build/ddfast/ddclaim.o &
    $CXX $FAST -c "$DDFAST/src/solver.cpp" -o build/ddfast/solver.o &
    $CXX $FAST -c "$DDFAST/src/api.cpp" -o build/ddfast/api.o &
    $CXX $FAST -c "$DDFAST/src/par_deal.cpp" -o build/ddfast/par_deal.o &
    wait
  }
  rm -f build/ddfast/libddfast.a
  ar rcs build/ddfast/libddfast.a build/ddfast/solver.o build/ddfast/api.o build/ddfast/par_deal.o build/ddfast/ddclaim.o
  FAST_FLAGS="-DWITH_DDFAST -I$DDFAST/include"
  FAST_LIBS="build/ddfast/libddfast.a -pthread"
  echo "built build/ddfast/libddfast.a"
else
  echo "ddfast not built (needs third_party/ddfast, and AVX-512 and BMI2)"
fi

# shellcheck disable=SC2086
$CXX -std=c++20 -O2 -Ithird_party/dds/library/src -Itools $FAST_FLAGS tools/ddscert.cpp build/dds/libdds.a $FAST_LIBS -o build/ddscert
$CXX -std=c++20 -O2 -Ithird_party/dds/library/src tools/ddspar.cpp build/dds/libdds.a -o build/ddspar
lake build
