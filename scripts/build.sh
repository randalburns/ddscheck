#!/bin/sh
# Build everything: DDS, the certificate generator, and the Lean checker.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
scripts/build_dds.sh
clang++ -std=c++20 -O2 -Ithird_party/dds/library/src -Itools tools/ddscert.cpp build/dds/libdds.a -o build/ddscert
clang++ -std=c++20 -O2 -Ithird_party/dds/library/src tools/ddspar.cpp build/dds/libdds.a -o build/ddspar
lake build
