// Writes random small endgames with DDS's answers, for tests/SpecVsDds.lean to compare with
// a direct evaluation of the Lean `value` function. No certificates are involved, so this
// tests the rules specification itself.
//
// Each line: strain leader dds_ns_tricks n1 c... e1 c... s1 c... w1 c... (card = suit*16+rank)
#include <api/dll.h>

#include <algorithm>
#include <cstdio>
#include <random>
#include <vector>

int main(int argc, char** argv) {
  int per_size = argc > 1 ? atoi(argv[1]) : 200;
  SetMaxThreads(1);
  std::mt19937 rng(2026);
  for (int size = 1; size <= 4; size++)
    for (int n = 0; n < per_size; n++) {
      std::vector<int> deck(52);
      for (int i = 0; i < 52; i++) deck[i] = i;
      std::shuffle(deck.begin(), deck.end(), rng);
      // Concentrate the cards in fewer suits now and then, so that voids and ruffs are common.
      if (n % 2 == 0) {
        std::stable_partition(deck.begin(), deck.end(), [](int c) { return c / 13 < 2; });
        std::shuffle(deck.begin(), deck.begin() + 26, rng);
      }
      Deal deal{};
      deal.trump = n % 5;
      deal.first = rng() % 4;
      std::vector<int> hands[4];
      for (int i = 0; i < 4 * size; i++) {
        int seat = i % 4, suit = deck[i] / 13, rank = 2 + deck[i] % 13;
        deal.remainCards[seat][suit] |= 1 << rank;
        hands[seat].push_back(suit * 16 + rank);
      }
      FutureTricks answer{};
      int rc = SolveBoard(deal, -1, 1, 1, &answer, 0);
      if (rc != RETURN_NO_FAULT) {
        fprintf(stderr, "DDS failed: %d\n", rc);
        return 2;
      }
      int to_lead_side = deal.first & 1;
      int ns = to_lead_side == 0 ? answer.score[0] : size - answer.score[0];
      printf("%d %d %d", deal.trump, deal.first, ns);
      for (auto& h : hands) {
        printf(" %zu", h.size());
        for (int c : h) printf(" %d", c);
      }
      printf("\n");
    }
}
