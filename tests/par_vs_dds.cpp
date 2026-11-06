// Writes double-dummy tables with DDS's DealerPar scores, for tests/ParVsDds.lean to compare
// with the Lean par evaluator. Half the point is the altered tables: on real deals the dealer
// almost never changes par, but small changes to a table make it happen.
//
// Usage: par_vs_dds <deals> <altered tables per deal> <seed>
// Each line: 20 table entries (S H D C NT by N E S W), vulnerability (0 none, 1 both, 2 NS,
// 3 EW), dealer (0 N, 1 E, 2 S, 3 W), DDS's score.
#include <api/dll.h>

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

namespace {

void compare_line(const DdTableResults& table, int vul, int dealer) {
  ParResultsDealer par{};
  if (DealerPar(&table, &par, dealer, vul) != RETURN_NO_FAULT) return;
  for (int s = 0; s < 5; s++)
    for (int h = 0; h < 4; h++) printf("%d ", table.res_table[s][h]);
  printf("%d %d %d\n", vul, dealer, par.score);
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: par_vs_dds <deals> <altered per deal> <seed>\n");
    return 2;
  }
  int deals = atoi(argv[1]), altered = atoi(argv[2]);
  std::mt19937 rng(atoi(argv[3]));
  SetMaxThreads(1);
  for (int k = 0; k < deals; k++) {
    std::vector<int> deck(52);
    for (int i = 0; i < 52; i++) deck[i] = i;
    std::shuffle(deck.begin(), deck.end(), rng);
    DdTableDeal deal{};
    for (int i = 0; i < 52; i++) deal.cards[i / 13][deck[i] / 13] |= 1 << (2 + deck[i] % 13);
    DdTableResults real{};
    if (CalcDDtable(deal, &real) != RETURN_NO_FAULT) return 2;
    for (int vul = 0; vul < 4; vul++)
      for (int dealer = 0; dealer < 4; dealer++) compare_line(real, vul, dealer);
    for (int a = 0; a < altered; a++) {
      DdTableResults t = real;
      int changes = 1 + rng() % 4;
      for (int c = 0; c < changes; c++) {
        int s = rng() % 5, h = rng() % 4, delta = static_cast<int>(rng() % 5) - 2;
        t.res_table[s][h] = std::clamp(t.res_table[s][h] + delta, 0, 13);
      }
      compare_line(t, rng() % 4, rng() % 4);
    }
    fflush(stdout);
  }
}
