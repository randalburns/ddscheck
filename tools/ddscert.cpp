// ddscert: turn DDS's double-dummy answers into certificates for `ddscheck`.
//
// DDS is treated as an untrusted oracle. For each result in its table we build a strategy
// for North-South and one for East-West, asking DDS which card to play on the proving
// side's turns and trying every legal card on the opponents' turns. If DDS were wrong,
// either this search would hit a contradiction or ddscheck would reject the output.
//
// With --solver own, the results and moves come from altsolve instead, so DDS plays no part in
// the certificate. With --solver ddfast they come from ddfast (third_party/ddfast), which only
// values positions at the start of a trick: a card in the middle of a trick is chosen by
// searching the rest of the trick here and asking ddfast for the positions after it. Either
// way DDS's table is still computed, and any disagreement is reported.
//
// Usage: ddscert --pbn "N:AKQ.... ..." [--strain S|H|D|C|N --declarer N|E|S|W]
//                [--solver dds|own|ddfast] -o out.cert
#include <api/dll.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <memory>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "altsolve.hpp"
#ifdef WITH_DDFAST
#include "ddfast.hpp"
#endif

namespace {

using Bytes = std::vector<uint8_t>;

// holding[seat][suit]: bit r is rank r (2..14). Seats and suits use DDS's numbering, and
// the order of suits and ranks here must match the order of cards in the Lean lists.
struct Layout {
  std::array<std::array<uint16_t, 4>, 4> holding{};
};
struct Play {
  int seat, suit, rank;
};

int g_trump;
Bytes g_entries;
size_t g_facts;
size_t g_oracle_calls;
altsolve::Solver* g_own;  // null when DDS supplies the moves
bool g_ddfast;            // ddfast supplies the moves
bool g_ddfast_keep;       // ddfast may keep its search table (same strain as its last call)
std::unordered_map<std::string, int> g_value_cache;  // ddfast's values, by canonical position
std::unordered_map<std::string, std::pair<int, size_t>> g_proven;
std::unordered_map<std::string, FutureTricks> g_oracle_cache;

void put_varint(Bytes& out, size_t v) {
  while (v >= 128) {
    out.push_back(128 | (v & 127));
    v >>= 7;
  }
  out.push_back(v);
}

uint8_t card_byte(int suit, int rank) { return suit * 16 + (rank - 2); }

// Canonical layouts keep rank k in bit k + 2 (see `canonical`), and are written as k.
// The deal itself is written with its true ranks, 2..14.
void put_hands(Bytes& out, const Layout& p, int rank_shift = 2) {
  for (int seat = 0; seat < 4; seat++) {
    out.push_back(__builtin_popcount(p.holding[seat][0]) + __builtin_popcount(p.holding[seat][1]) +
                  __builtin_popcount(p.holding[seat][2]) + __builtin_popcount(p.holding[seat][3]));
    for (int suit = 0; suit < 4; suit++)
      for (int r = 14; r >= 2; r--)
        if (p.holding[seat][suit] >> r & 1) out.push_back(suit * 16 + (r - rank_shift));
  }
}

// Mirrors `canon` in Lean: each rank becomes the number of remaining cards of its suit
// below it (stored here shifted up by 2).
Layout canonical(const Layout& p) {
  Layout out;
  for (int suit = 0; suit < 4; suit++) {
    int below = 0;
    for (int r = 2; r <= 14; r++) {
      bool found = false;
      for (int seat = 0; seat < 4; seat++)
        if (p.holding[seat][suit] >> r & 1) {
          out.holding[seat][suit] |= 1 << (below + 2);
          found = true;
        }
      below += found;
    }
  }
  return out;
}

std::string key_of(const Layout& p, int turn) {
  std::string k(reinterpret_cast<const char*>(&p.holding), sizeof p.holding);
  k.push_back(static_cast<char>(turn));
  return k;
}

const FutureTricks& ask_oracle(const Layout& p, int leader, const std::vector<Play>& trick) {
  std::string k = key_of(p, leader);
  for (const Play& t : trick) {
    k.push_back(static_cast<char>(t.suit));
    k.push_back(static_cast<char>(t.rank));
  }
  auto it = g_oracle_cache.find(k);
  if (it != g_oracle_cache.end()) return it->second;

  Deal deal{};
  deal.trump = g_trump;
  deal.first = leader;
  for (size_t i = 0; i < trick.size(); i++) {
    deal.currentTrickSuit[i] = trick[i].suit;
    deal.currentTrickRank[i] = trick[i].rank;
  }
  for (int seat = 0; seat < 4; seat++)
    for (int suit = 0; suit < 4; suit++) deal.remainCards[seat][suit] = p.holding[seat][suit];
  FutureTricks answer{};
  int rc = SolveBoard(deal, -1, 3, 1, &answer, 0);
  g_oracle_calls++;
  if (rc != RETURN_NO_FAULT) {
    char message[80];
    ErrorMessage(rc, message);
    fprintf(stderr, "DDS error: %s\n", message);
    exit(2);
  }
  return g_oracle_cache.emplace(std::move(k), answer).first->second;
}

bool beats(const Play& a, const Play& best) {
  if (a.suit == best.suit) return a.rank > best.rank;
  return a.suit == g_trump;
}

size_t prove(const Layout& position, int leader, int side, int need);

// North-South's tricks from a position at the start of a trick, from ddfast (untrusted).
int ddfast_ns(const Layout& position, int leader) {
  Layout p = canonical(position);
  std::string k = key_of(p, leader);
  auto it = g_value_cache.find(k);
  if (it != g_value_cache.end()) return it->second;
  int v = -1;
#ifdef WITH_DDFAST
  ddfast::Position q{};
  for (int seat = 0; seat < 4; seat++)
    for (int suit = 0; suit < 4; suit++) q.hand[seat][suit] = p.holding[seat][suit] >> 2;
  q.trump = g_trump;
  q.leader = leader;
  v = ddfast::solve_position(q, g_ddfast_keep);
  g_ddfast_keep = true;
#endif
  g_oracle_calls++;
  if (v < 0) {
    fprintf(stderr, "ddfast error: bad position\n");
    exit(2);
  }
  g_value_cache.emplace(std::move(k), v);
  return v;
}

int cards_left(const Layout& p, int seat) {
  int n = 0;
  for (int suit = 0; suit < 4; suit++) n += __builtin_popcount(p.holding[seat][suit]);
  return n;
}

// The legal cards of `seat`, one per run of equivalent cards: cards of one suit in one hand
// with no remaining card of another hand, nor a card of this trick, between them.
std::vector<std::pair<int, int>> distinct_cards(const Layout& p, int seat, const std::vector<Play>& trick) {
  std::vector<std::pair<int, int>> out;
  int led = trick.empty() ? -1 : trick[0].suit;
  bool follows = led >= 0 && p.holding[seat][led] != 0;
  for (int suit = 0; suit < 4; suit++) {
    if (follows && suit != led) continue;
    uint16_t others = 0;
    for (int s = 0; s < 4; s++)
      if (s != seat) others |= p.holding[s][suit];
    for (const Play& t : trick)
      if (t.suit == suit) others |= 1 << t.rank;
    bool run = false;
    for (int r = 14; r >= 2; r--) {
      if (p.holding[seat][suit] >> r & 1) {
        if (!run) out.push_back({suit, r});
        run = true;
      } else if (others >> r & 1) {
        run = false;
      }
    }
  }
  return out;
}

// Whether `side` can take `need` tricks from here, `trick` being the cards played so far to
// this trick: a search of the rest of the trick, with ddfast's values once it is over.
bool fast_reaches(Layout& p, int leader, int side, int need, std::vector<Play>& trick) {
  if (need <= 0) return true;
  if (trick.size() == 4) {
    Play best = trick[0];
    for (int i = 1; i < 4; i++)
      if (beats(trick[i], best)) best = trick[i];
    int next_need = need - ((best.seat & 1) == side ? 1 : 0);
    if (next_need <= 0) return true;
    int left = cards_left(p, 0);
    if (next_need > left) return false;
    int ns = ddfast_ns(p, best.seat);
    return (side == 0 ? ns : left - ns) >= next_need;
  }
  int seat = (leader + static_cast<int>(trick.size())) % 4;
  bool ours = (seat & 1) == side;
  for (auto [suit, rank] : distinct_cards(p, seat, trick)) {
    p.holding[seat][suit] &= ~(1 << rank);
    trick.push_back({seat, suit, rank});
    bool works = fast_reaches(p, leader, side, need, trick);
    trick.pop_back();
    p.holding[seat][suit] |= 1 << rank;
    if (works == ours) return ours;
  }
  return !ours;
}

// How many replies the opponents have in the rest of this trick if the proving side plays a
// card of `suit` now. Choosing a card that keeps this small keeps the certificate small.
size_t opponent_replies(const Layout& p, int leader, int side, const std::vector<Play>& trick,
                        int suit) {
  int led = trick.empty() ? suit : trick[0].suit;
  size_t replies = 1;
  for (size_t i = trick.size() + 1; i < 4; i++) {
    int seat = (leader + static_cast<int>(i)) % 4;
    if ((seat & 1) == side) continue;
    int in_suit = __builtin_popcount(p.holding[seat][led]);
    if (in_suit == 0)
      for (int d = 0; d < 4; d++) in_suit += __builtin_popcount(p.holding[seat][d]);
    replies *= in_suit;
  }
  return replies;
}

void walk(Layout& p, int leader, int side, int need, std::vector<Play>& trick, Bytes& out) {
  if (need <= 0) {  // ddscheck accepts anything here; write the shortest tree
    out.push_back(0);
    put_varint(out, 0);
    return;
  }
  if (trick.size() == 4) {
    Play best = trick[0];
    for (int i = 1; i < 4; i++)
      if (beats(trick[i], best)) best = trick[i];
    int next_need = need - ((best.seat & 1) == side ? 1 : 0);
    if (next_need <= 0) {
      out.push_back(0);
      put_varint(out, 0);
      return;
    }
    out.push_back(0);
    put_varint(out, prove(p, best.seat, side, next_need));
    return;
  }

  int seat = (leader + static_cast<int>(trick.size())) % 4;
  auto play_and_walk = [&](int suit, int rank) {
    p.holding[seat][suit] &= ~(1 << rank);
    trick.push_back({seat, suit, rank});
    walk(p, leader, side, need, trick, out);
    trick.pop_back();
    p.holding[seat][suit] |= 1 << rank;
  };

  if ((seat & 1) == side && (g_own != nullptr || g_ddfast)) {
    // Try the cards leaving the opponents the fewest replies first.
    std::vector<std::tuple<size_t, int, int>> candidates;
    for (int suit = 0; suit < 4; suit++) {
      if (!trick.empty() && p.holding[seat][trick[0].suit] != 0 && suit != trick[0].suit) continue;
      for (int r = 14; r >= 2; r--)
        if (p.holding[seat][suit] >> r & 1)
          candidates.push_back({opponent_replies(p, leader, side, trick, suit), suit, -r});
    }
    std::sort(candidates.begin(), candidates.end());
    int left = 0;
    for (int suit = 0; suit < 4; suit++) left += __builtin_popcount(p.holding[seat][suit]);
    for (auto [replies, suit, negative_rank] : candidates) {
      int rank = -negative_rank;
      if (g_ddfast) {
        p.holding[seat][suit] &= ~(1 << rank);
        trick.push_back({seat, suit, rank});
        bool works = fast_reaches(p, leader, side, need, trick);
        trick.pop_back();
        p.holding[seat][suit] |= 1 << rank;
        if (works) {
          out.push_back(1);
          out.push_back(card_byte(suit, rank));
          play_and_walk(suit, rank);
          return;
        }
        continue;
      }
      altsolve::Holding after = p.holding;
      after[seat][suit] &= static_cast<uint16_t>(~(1 << rank));
      std::vector<altsolve::Play> plays;
      for (const Play& t : trick) plays.push_back({t.seat, t.suit, t.rank});
      plays.push_back({seat, suit, rank});
      g_oracle_calls++;
      // East-West taking `need` of the `left` tricks means North-South cannot reach the rest + 1.
      bool works = side == 0 ? g_own->ns_reaches(after, leader, plays, need)
                             : !g_own->ns_reaches(after, leader, plays, left - need + 1);
      if (works) {
        out.push_back(1);
        out.push_back(card_byte(suit, rank));
        play_and_walk(suit, rank);
        return;
      }
    }
    fprintf(stderr, "%s contradicts itself: no card takes the %d tricks it promised\n", g_ddfast ? "ddfast" : "altsolve", need);
    exit(3);
  }

  if ((seat & 1) == side) {
    // Copy: the recursion below can grow the cache.
    const FutureTricks answer = ask_oracle(p, leader, trick);
    int chosen = -1;
    size_t fewest = SIZE_MAX;
    for (int i = 0; i < answer.cards; i++) {
      if (answer.score[i] < need) continue;
      size_t replies = opponent_replies(p, leader, side, trick, answer.suit[i]);
      if (replies < fewest) {
        fewest = replies;
        chosen = i;
      }
    }
    if (chosen >= 0) {
      out.push_back(1);
      out.push_back(card_byte(answer.suit[chosen], answer.rank[chosen]));
      play_and_walk(answer.suit[chosen], answer.rank[chosen]);
      return;
    }
    fprintf(stderr, "DDS contradicts itself: no card takes the %d tricks it promised\n", need);
    exit(3);
  }

  int led = trick.empty() ? -1 : trick[0].suit;
  bool follows = led >= 0 && p.holding[seat][led] != 0;
  out.push_back(2);
  size_t count = 0;
  for (int suit = 0; suit < 4; suit++)
    if (!follows || suit == led) count += __builtin_popcount(p.holding[seat][suit]);
  out.push_back(count);
  for (int suit = 0; suit < 4; suit++) {
    if (follows && suit != led) continue;
    for (int r = 14; r >= 2; r--)
      if (p.holding[seat][suit] >> r & 1) play_and_walk(suit, r);
  }
}

// Add a fact "side takes at least `need` from this position" and return its index.
size_t prove(const Layout& position, int leader, int side, int need) {
  Layout p = canonical(position);
  std::string k = key_of(p, leader);
  k.push_back(static_cast<char>(side));
  auto it = g_proven.find(k);
  if (it != g_proven.end() && it->second.first >= need) return it->second.second;

  Bytes body;
  std::vector<Play> trick;
  Layout working = p;
  walk(working, leader, side, need, trick, body);

  put_hands(g_entries, p);
  g_entries.push_back(leader);
  g_entries.push_back(side);
  g_entries.push_back(need);
  g_entries.insert(g_entries.end(), body.begin(), body.end());
  size_t index = g_facts++;
  g_proven[k] = {need, index};
  return index;
}

void parse_pbn(const std::string& pbn, Layout& p) {
  const std::string seats = "NESW", ranks = "23456789TJQKA";
  size_t first = seats.find(pbn.at(0));
  if (first == std::string::npos || pbn.at(1) != ':') {
    fprintf(stderr, "bad PBN deal\n");
    exit(2);
  }
  int seat = static_cast<int>(first), suit = 0;
  for (size_t i = 2; i < pbn.size(); i++) {
    char c = pbn[i];
    if (c == ' ') {
      seat = (seat + 1) % 4;
      suit = 0;
    } else if (c == '.') {
      suit++;
    } else {
      size_t r = ranks.find(c);
      if (r == std::string::npos || suit > 3) {
        fprintf(stderr, "bad PBN deal\n");
        exit(2);
      }
      p.holding[seat][suit] |= 1 << (r + 2);
    }
  }
}

void add_claim(Bytes& file, const Layout& deal, int strain, int declarer, int declarer_tricks) {
  int leader = (declarer + 1) % 4;
  int ns_tricks = (declarer & 1) == 0 ? declarer_tricks : 13 - declarer_tricks;

  g_trump = strain;
  g_entries.clear();
  g_facts = 0;
  g_proven.clear();
  g_oracle_cache.clear();
  g_value_cache.clear();
  g_ddfast_keep = false;
  g_oracle_calls = 0;
  if (g_own != nullptr) g_own->set_trump(strain);

  auto root = [&](int side, int need) -> size_t {
    if (need > 0) return prove(deal, leader, side, need);
    // A trivial entry: a need of zero holds with any tree.
    put_hands(g_entries, canonical(deal));
    g_entries.push_back(leader);
    g_entries.push_back(side);
    g_entries.push_back(0);
    g_entries.push_back(0);
    put_varint(g_entries, 0);
    return g_facts++;
  };
  auto start = std::chrono::steady_clock::now();
  size_t ns_fact = root(0, ns_tricks);
  size_t ew_fact = root(1, 13 - ns_tricks);
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();

  file.push_back(strain);
  file.push_back(leader);
  file.push_back(ns_tricks);
  put_hands(file, deal, 0);
  put_varint(file, g_facts);
  file.insert(file.end(), g_entries.begin(), g_entries.end());
  put_varint(file, ns_fact);
  put_varint(file, ew_fact);

  printf("%-2s by %c: claim is declarer takes %2d  | %8zu facts, %9zu bytes, %8zu oracle calls, %.1fs\n",
         strain == 4 ? "NT" : std::string(1, "SHDC"[strain]).c_str(), "NESW"[declarer],
         declarer_tricks, g_facts, g_entries.size(), g_oracle_calls, secs);
  fflush(stdout);
}

}  // namespace

int main(int argc, char** argv) {
  std::string pbn, out_path, solver_name = "dds";
  int only_strain = -1, only_declarer = -1;
  for (int i = 1; i + 1 < argc; i += 2) {
    std::string flag = argv[i], value = argv[i + 1];
    if (flag == "--pbn") pbn = value;
    else if (flag == "-o") out_path = value;
    else if (flag == "--strain") only_strain = std::string("SHDCN").find(value.at(0));
    else if (flag == "--declarer") only_declarer = std::string("NESW").find(value.at(0));
    else if (flag == "--solver") solver_name = value;
    else {
      fprintf(stderr, "unknown flag %s\n", flag.c_str());
      return 2;
    }
  }
  if (pbn.empty() || out_path.empty()) {
    fprintf(stderr, "usage: ddscert --pbn \"N:...\" [--strain S|H|D|C|N --declarer N|E|S|W] [--solver dds|own|ddfast] -o out.cert\n");
    return 2;
  }

  SetMaxThreads(1);
  Layout deal;
  parse_pbn(pbn, deal);

  DdTableDeal table_deal{};
  for (int seat = 0; seat < 4; seat++)
    for (int suit = 0; suit < 4; suit++) table_deal.cards[seat][suit] = deal.holding[seat][suit];
  DdTableResults table{};
  int rc = CalcDDtable(table_deal, &table);
  if (rc != RETURN_NO_FAULT) {
    char message[80];
    ErrorMessage(rc, message);
    fprintf(stderr, "DDS error: %s\n", message);
    return 2;
  }

  altsolve::Options own_options;
  own_options.table_bits = 24;
  std::unique_ptr<altsolve::Solver> own;
  if (solver_name == "own") {
    own = std::make_unique<altsolve::Solver>(own_options);
    g_own = own.get();
  } else if (solver_name == "ddfast") {
#ifdef WITH_DDFAST
    ddfast::init(nullptr);  // the tables in $DDFAST_TABLES, built there on first use
    g_ddfast = true;
#else
    fprintf(stderr, "this ddscert was built without ddfast\n");
    return 2;
#endif
  } else if (solver_name != "dds") {
    fprintf(stderr, "unknown solver %s\n", solver_name.c_str());
    return 2;
  }

#ifdef WITH_DDFAST
  ddfast::Table fast_table{};
  if (g_ddfast) {
    ddfast::Deal fast_deal{};
    for (int seat = 0; seat < 4; seat++)
      for (int suit = 0; suit < 4; suit++) fast_deal.hand[seat][suit] = deal.holding[seat][suit] >> 2;
    ddfast::solve_table(fast_deal, fast_table);
  }
#endif

  Bytes file;
  for (int strain = 0; strain < 5; strain++)
    for (int declarer = 0; declarer < 4; declarer++) {
      if (only_strain >= 0 && strain != only_strain) continue;
      if (only_declarer >= 0 && declarer != only_declarer) continue;
      int tricks = table.res_table[strain][declarer];
      if (g_own != nullptr) {
        g_own->set_trump(strain);
        int ns = g_own->ns_value(deal.holding, (declarer + 1) % 4, {});
        int own_tricks = (declarer & 1) == 0 ? ns : 13 - ns;
        if (own_tricks != tricks)
          printf("DISAGREE strain %d declarer %d: DDS %d, altsolve %d\n", strain, declarer, tricks, own_tricks);
        tricks = own_tricks;
      }
#ifdef WITH_DDFAST
      if (g_ddfast) {
        int fast_tricks = fast_table.tricks[strain][declarer];
        if (fast_tricks != tricks)
          printf("DISAGREE strain %d declarer %d: DDS %d, ddfast %d\n", strain, declarer, tricks, fast_tricks);
        tricks = fast_tricks;
      }
#endif
      add_claim(file, deal, strain, declarer, tricks);
    }
  std::ofstream(out_path, std::ios::binary)
      .write(reinterpret_cast<const char*>(file.data()), static_cast<std::streamsize>(file.size()));
  printf("wrote %s (%zu bytes)\n", out_path.c_str(), file.size());
}
