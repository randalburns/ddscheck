// Directed test of DDS, aimed at quick_tricks and later_tricks, against solvers that share no
// code with it: a brute-force solver for small positions (up to about 6 tricks), and altsolve
// for larger ones. In `both` mode the two are also compared with each other.
//
// Every position is checked three ways:
//   - exact score of every legal card (solutions = 3)
//   - exact score and a best card (solutions = 1)
//   - every target: reachable or not, and whether the card returned really reaches it
//
// Usage: dds_stress <seconds> <seed> [max tricks] [brute|smart|both] [min tricks]
#include <api/dll.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "../tools/altsolve.hpp"

namespace {

using Holding = std::array<std::array<uint16_t, 4>, 4>;  // [seat][suit], bit r = rank r
struct Play {
  int seat, suit, rank;
};

int g_trump;
std::unordered_map<std::string, int> g_memo;

int count_cards(const Holding& h, int seat) {
  int n = 0;
  for (int s = 0; s < 4; s++) n += __builtin_popcount(h[seat][s]);
  return n;
}

bool wins_over(const Play& a, const Play& best) {
  if (a.suit == best.suit) return a.rank > best.rank;
  return a.suit == g_trump;
}

// Tricks North-South take from here on with best play by both sides.
int ns_value(Holding& h, int leader, std::vector<Play>& trick);

int ns_after_card(Holding& h, int leader, std::vector<Play>& trick, int seat, int suit, int rank) {
  h[seat][suit] &= ~(1 << rank);
  trick.push_back({seat, suit, rank});
  int v;
  if (trick.size() == 4) {
    Play best = trick[0];
    for (int i = 1; i < 4; i++)
      if (wins_over(trick[i], best)) best = trick[i];
    std::vector<Play> next;
    v = ((best.seat & 1) == 0 ? 1 : 0) + ns_value(h, best.seat, next);
  } else {
    v = ns_value(h, leader, trick);
  }
  trick.pop_back();
  h[seat][suit] |= 1 << rank;
  return v;
}

std::vector<std::pair<int, int>> legal_cards(const Holding& h, int seat, const std::vector<Play>& trick) {
  std::vector<std::pair<int, int>> out;
  int led = trick.empty() ? -1 : trick[0].suit;
  bool follows = led >= 0 && h[seat][led] != 0;
  for (int s = 0; s < 4; s++) {
    if (follows && s != led) continue;
    for (int r = 14; r >= 2; r--)
      if (h[seat][s] >> r & 1) out.push_back({s, r});
  }
  return out;
}

int ns_value(Holding& h, int leader, std::vector<Play>& trick) {
  int seat = (leader + static_cast<int>(trick.size())) % 4;
  std::string key;
  if (trick.empty()) {
    if (count_cards(h, seat) == 0) return 0;
    key.assign(reinterpret_cast<const char*>(&h), sizeof h);
    key.push_back(static_cast<char>(leader));
    auto it = g_memo.find(key);
    if (it != g_memo.end()) return it->second;
  }
  int best = (seat & 1) == 0 ? -1 : 100;
  for (auto [suit, rank] : legal_cards(h, seat, trick)) {
    int v = ns_after_card(h, leader, trick, seat, suit, rank);
    best = (seat & 1) == 0 ? std::max(best, v) : std::min(best, v);
  }
  if (trick.empty()) g_memo.emplace(std::move(key), best);
  return best;
}

// ---- Position generators ----

std::mt19937 g_rng;
int rnd(int n) { return static_cast<int>(g_rng() % static_cast<unsigned>(n)); }

// Give each listed (card, preferred seat) to that seat if there is room, else to any seat.
Holding deal_out(const std::vector<std::pair<int, int>>& wanted, int size) {
  Holding h{};
  int have[4] = {0, 0, 0, 0};
  std::vector<int> overflow;
  for (auto [card, seat] : wanted) {
    if (seat >= 0 && have[seat] < size) {
      h[seat][card / 13] |= 1 << (2 + card % 13);
      have[seat]++;
    } else {
      overflow.push_back(card);
    }
  }
  for (int card : overflow) {
    int order[4] = {0, 1, 2, 3};
    std::shuffle(order, order + 4, g_rng);
    for (int seat : order)
      if (have[seat] < size) {
        h[seat][card / 13] |= 1 << (2 + card % 13);
        have[seat]++;
        break;
      }
  }
  return h;
}

// Card index: suit * 13 + rank offset, where offset 12 is the ace.
Holding generate(int kind, int size) {
  std::vector<std::pair<int, int>> wanted;
  std::vector<int> deck(52);
  for (int i = 0; i < 52; i++) deck[i] = i;
  std::shuffle(deck.begin(), deck.end(), g_rng);
  int total = 4 * size;

  switch (kind) {
    case 0:  // Uniform.
      for (int i = 0; i < total; i++) wanted.push_back({deck[i], -1});
      break;
    case 1: {  // Few suits, so voids and ruffs are everywhere.
      int a = rnd(4), b = (a + 1 + rnd(3)) % 4;
      std::stable_partition(deck.begin(), deck.end(), [&](int c) { return c / 13 == a || c / 13 == b; });
      std::shuffle(deck.begin(), deck.begin() + 26, g_rng);
      for (int i = 0; i < total; i++) wanted.push_back({deck[i], -1});
      break;
    }
    case 2: {  // One hand holds runs of top cards, so quick tricks matter.
      int owner = rnd(4);
      int partner = (owner + 2) % 4;
      int got = 0;
      for (int s = 0; s < 4 && got < total; s++) {
        int run = rnd(size + 1);
        for (int k = 0; k < run && got < total; k++, got++)
          wanted.push_back({s * 13 + 12 - k, rnd(5) == 0 ? partner : owner});
      }
      for (int i = 0; i < 52 && got < total; i++) {
        bool used = false;
        for (auto& w : wanted) used = used || w.first == deck[i];
        if (!used) {
          wanted.push_back({deck[i], -1});
          got++;
        }
      }
      break;
    }
    case 3: {  // Winners stranded in one hand, with no entry to it in partner's hand.
      int owner = rnd(4), partner = (owner + 2) % 4, side_suit = rnd(4);
      int run = 1 + rnd(size);
      int got = 0;
      for (int k = 0; k < run; k++, got++) wanted.push_back({side_suit * 13 + 12 - k, owner});
      for (int i = 0; i < 52 && got < total; i++) {
        int c = deck[i];
        bool used = false;
        for (auto& w : wanted) used = used || w.first == c;
        if (used) continue;
        int pref = -1;
        if (c / 13 == side_suit) pref = rnd(2) ? (owner + 1) % 4 : (owner + 3) % 4;
        else if (c % 13 < 6) pref = partner;  // low cards only, so partner has no entries
        wanted.push_back({c, pref});
        got++;
      }
      break;
    }
    default: {  // Sparse ranks: few cards from all over each suit, with big gaps.
      std::vector<int> picks;
      for (int s = 0; s < 4; s++) {
        int ranks[13];
        for (int r = 0; r < 13; r++) ranks[r] = r;
        std::shuffle(ranks, ranks + 13, g_rng);
        int take = std::min(13, total / 4 + rnd(3));
        for (int k = 0; k < take; k++) picks.push_back(s * 13 + ranks[k]);
      }
      std::shuffle(picks.begin(), picks.end(), g_rng);
      for (int i = 0; i < total && i < static_cast<int>(picks.size()); i++) wanted.push_back({picks[i], -1});
      for (int i = 0; static_cast<int>(wanted.size()) < total; i++) {
        bool used = false;
        for (auto& w : wanted) used = used || w.first == deck[i];
        if (!used) wanted.push_back({deck[i], -1});
      }
      break;
    }
  }
  return deal_out(wanted, size);
}

// ---- Comparison ----

long g_positions, g_calls, g_errors;
std::string g_mode = "brute";
altsolve::Solver* g_smart;
long g_by_kind[5];

void report(const char* what, const Holding& h, int leader, const std::vector<Play>& trick, int target,
            int got, int want) {
  g_errors++;
  if (g_errors > 25) return;
  printf("MISMATCH %s: trump=%d leader=%d target=%d DDS=%d brute=%d holdings=", what, g_trump, leader, target,
         got, want);
  for (int seat = 0; seat < 4; seat++) {
    for (int s = 0; s < 4; s++) printf("%x,", h[seat][s]);
    printf(" ");
  }
  printf("trick=");
  for (const Play& p : trick) printf("%d:%d:%d ", p.seat, p.suit, p.rank);
  printf("\n");
  fflush(stdout);
}

bool call_dds(const Holding& h, int leader, const std::vector<Play>& trick, int target, int solutions,
              FutureTricks& out) {
  Deal deal{};
  deal.trump = g_trump;
  deal.first = leader;
  for (size_t i = 0; i < trick.size(); i++) {
    deal.currentTrickSuit[i] = trick[i].suit;
    deal.currentTrickRank[i] = trick[i].rank;
  }
  for (int seat = 0; seat < 4; seat++)
    for (int s = 0; s < 4; s++) deal.remainCards[seat][s] = h[seat][s];
  g_calls++;
  int rc = SolveBoard(deal, target, solutions, 1, &out, 0);
  if (rc != RETURN_NO_FAULT) {
    report("dds-error-code", h, leader, trick, target, rc, RETURN_NO_FAULT);
    return false;
  }
  return true;
}

void check_position(Holding& h, int leader, std::vector<Play>& trick) {
  g_positions++;
  int seat = (leader + static_cast<int>(trick.size())) % 4;
  int side = seat & 1;
  // Tricks still to finish, counting the one in progress.
  int remaining = count_cards(h, seat);

  auto to_side = [&](int ns_total) { return side == 0 ? ns_total : remaining - ns_total; };
  auto card_value = [&](int suit, int rank) {
    int brute = -1, smart = -1;
    if (g_mode != "smart") brute = to_side(ns_after_card(h, leader, trick, seat, suit, rank));
    if (g_mode != "brute") {
      std::vector<altsolve::Play> plays;
      for (const Play& p : trick) plays.push_back({p.seat, p.suit, p.rank});
      smart = g_smart->value_after_card(h, leader, plays, suit, rank);
    }
    if (g_mode == "both" && brute != smart) report("solvers-disagree", h, leader, trick, suit * 100 + rank, smart, brute);
    return g_mode == "smart" ? smart : brute;
  };

  auto legal = legal_cards(h, seat, trick);
  int value = -1;
  std::vector<int> values;
  for (auto [suit, rank] : legal) {
    values.push_back(card_value(suit, rank));
    value = std::max(value, values.back());
  }

  // Score of every legal card. A listed card also stands for the lower cards in `equals`.
  FutureTricks all{};
  if (call_dds(h, leader, trick, -1, 3, all)) {
    std::vector<int> seen(legal.size(), 0);
    for (int i = 0; i < all.cards; i++) {
      for (size_t j = 0; j < legal.size(); j++) {
        bool same = legal[j].first == all.suit[i] && legal[j].second == all.rank[i];
        bool grouped = legal[j].first == all.suit[i] && (all.equals[i] >> legal[j].second & 1);
        if (same || grouped) {
          seen[j] = 1;
          if (all.score[i] != values[j])
            report("card-score", h, leader, trick, legal[j].first * 100 + legal[j].second, all.score[i], values[j]);
        }
      }
    }
    for (size_t j = 0; j < legal.size(); j++)
      if (!seen[j]) report("card-missing", h, leader, trick, legal[j].first * 100 + legal[j].second, -1, values[j]);
  }

  // Exact value and one best card.
  FutureTricks one{};
  if (call_dds(h, leader, trick, -1, 1, one)) {
    if (one.score[0] != value) report("best-score", h, leader, trick, -1, one.score[0], value);
    bool ok = false;
    for (size_t j = 0; j < legal.size(); j++)
      if (legal[j].first == one.suit[0] && legal[j].second == one.rank[0]) ok = values[j] == value;
    if (!ok) report("best-card", h, leader, trick, -1, one.suit[0] * 100 + one.rank[0], value);
  }

  // Every target: the part quick_tricks and later_tricks decide with their bounds.
  for (int t = 1; t <= remaining; t++) {
    FutureTricks tgt{};
    if (!call_dds(h, leader, trick, t, 1, tgt)) continue;
    bool reachable = value >= t;
    bool says = tgt.score[0] >= t;
    if (says != reachable) {
      report("target", h, leader, trick, t, tgt.score[0], value);
    } else if (reachable) {
      bool ok = false;
      for (size_t j = 0; j < legal.size(); j++)
        if (legal[j].first == tgt.suit[0] && legal[j].second == tgt.rank[0]) ok = values[j] >= t;
      if (!ok) report("target-card", h, leader, trick, t, tgt.suit[0] * 100 + tgt.rank[0], value);
    }
  }
}

}  // namespace

int main(int argc, char** argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: dds_stress <seconds> <seed> [max tricks]\n");
    return 2;
  }
  double budget = atof(argv[1]);
  g_rng.seed(atoi(argv[2]));
  int max_tricks = argc > 3 ? atoi(argv[3]) : 6;
  if (argc > 4) g_mode = argv[4];
  int min_tricks = argc > 5 ? atoi(argv[5]) : 2;
  altsolve::Options options;
  options.table_bits = 24;
  altsolve::Solver smart(options);
  g_smart = &smart;
  SetMaxThreads(1);
  auto start = std::chrono::steady_clock::now();
  while (std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() < budget) {
    int kind = rnd(5);
    int size = min_tricks + rnd(max_tricks - min_tricks + 1);
    g_trump = rnd(5);
    smart.set_trump(g_trump);
    Holding h = generate(kind, size);
    int leader = rnd(4);
    g_memo.clear();
    g_by_kind[kind]++;

    // Partly play the current trick half the time, with random legal cards.
    std::vector<Play> trick;
    int played = rnd(2) ? 0 : rnd(4);
    for (int i = 0; i < played; i++) {
      int seat = (leader + i) % 4;
      auto legal = legal_cards(h, seat, trick);
      auto [suit, rank] = legal[rnd(static_cast<int>(legal.size()))];
      h[seat][suit] &= ~(1 << rank);
      trick.push_back({seat, suit, rank});
    }
    check_position(h, leader, trick);
  }
  printf("positions=%ld calls=%ld errors=%ld kinds=%ld/%ld/%ld/%ld/%ld\n", g_positions, g_calls, g_errors,
         g_by_kind[0], g_by_kind[1], g_by_kind[2], g_by_kind[3], g_by_kind[4]);
  return g_errors == 0 ? 0 : 1;
}
