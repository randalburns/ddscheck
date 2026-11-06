// Measures what each altsolve technique contributes, and how the solver scales.
//
// Usage: solver_bench stages <tricks> <positions>   compare techniques at one size
//        solver_bench scale <tricks> <positions>    time the full solver at one size
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <string>

#include "../tools/altsolve.hpp"

using altsolve::Holding;
using altsolve::Options;

namespace {

Holding random_position(std::mt19937& rng, int tricks) {
  std::vector<int> deck(52);
  for (int i = 0; i < 52; i++) deck[i] = i;
  std::shuffle(deck.begin(), deck.end(), rng);
  Holding h{};
  for (int i = 0; i < 4 * tricks; i++) h[i % 4][deck[i] / 13] |= static_cast<uint16_t>(1 << (2 + deck[i] % 13));
  return h;
}

void run(const char* name, Options options, int tricks, int positions) {
  std::mt19937 rng(42);
  altsolve::Solver solver(options);
  double slowest = 0;
  auto start = std::chrono::steady_clock::now();
  long checksum = 0;
  for (int p = 0; p < positions; p++) {
    Holding h = random_position(rng, tricks);
    auto t0 = std::chrono::steady_clock::now();
    solver.set_trump(p % 5);
    checksum += solver.ns_value(h, p % 4, {});
    slowest = std::max(slowest, std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
  }
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
  printf("%-28s %8.3f s/position  slowest %8.3f s  %12.0f nodes/position  checksum %ld\n", name, secs / positions,
         slowest, static_cast<double>(solver.nodes()) / positions, checksum);
  fflush(stdout);
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: solver_bench stages|scale <tricks> <positions>\n");
    return 2;
  }
  std::string mode = argv[1];
  int tricks = atoi(argv[2]), positions = atoi(argv[3]);
  if (mode == "stages") {
    Options o;
    o.memo = o.merge = o.touching = o.ordering = false;
    run("alpha-beta only", o, tricks, positions);
    o.memo = true;
    run("+ remembered positions", o, tricks, positions);
    o.merge = true;
    run("+ relative ranks", o, tricks, positions);
    o.touching = true;
    run("+ touching cards", o, tricks, positions);
    o.ordering = true;
    run("+ move ordering", o, tricks, positions);
  } else {
    Options o;
    o.table_bits = 24;
    run("all techniques", o, tricks, positions);
  }
}
