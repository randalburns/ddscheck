#!/bin/sh
# Compile the vendored DDS library into build/dds/libdds.a with plain clang++,
# so the project needs neither Bazel nor any change to the DDS sources.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
DDS="$ROOT/third_party/dds"
OUT="$ROOT/build/dds"
mkdir -p "$OUT/obj"
cd "$DDS"

compile_one() {
  obj="$OUT/obj/$(echo "$1" | tr '/' '_').o"
  [ "$obj" -nt "$1" ] && return 0
  clang++ -std=c++20 -O3 -DNDEBUG -Ilibrary/src -c "$1" -o "$obj"
}

jobs=$(sysctl -n hw.ncpu)
running=0
for src in $(find library/src -name '*.cpp'); do
  compile_one "$src" &
  running=$((running + 1))
  if [ "$running" -ge "$jobs" ]; then
    wait
    running=0
  fi
done
wait

rm -f "$OUT/libdds.a"
ar rcs "$OUT/libdds.a" "$OUT"/obj/*.o
echo "built $OUT/libdds.a"
