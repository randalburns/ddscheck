// altsolve: a small double-dummy solver that shares no code with DDS.
//
// It exists to check DDS, so it deliberately has no quick-trick or later-trick shortcuts and no
// partial-rank reuse of table entries: only target search with alpha-beta cutoffs, a table of
// bounds keyed on relative ranks, touching-card merging and simple move ordering.
//
// Its answers are not trusted either: it is tested against brute force and DDS, and `ddscert
// --solver own` turns its answers into certificates for Lean to check.
#pragma once

#include <algorithm>
#include <array>
#include <cstdint>
#include <vector>

namespace altsolve {

// holding[seat][suit]: bit r is rank r (2..14). Seats N E S W are 0..3, suits S H D C are 0..3.
using Holding = std::array<std::array<uint16_t, 4>, 4>;

constexpr int kNoTrump = 4;

struct Play {
  int seat, suit, rank;
};

struct Options {
  bool memo = true;      // remember bounds for positions at the start of a trick
  bool merge = true;     // share them between positions with the same relative ranks
  bool touching = true;  // try only one of a run of touching cards
  bool ordering = true;  // try likely winners first
  int table_bits = 22;   // table of 2^table_bits entries, 40 bytes each
};

class Solver {
 public:
  explicit Solver(Options options = Options()) : options_(options) {
    if (options_.memo) table_.resize(size_t{1} << options_.table_bits);
  }

  // Bounds depend on the trump suit, so changing it clears the table.
  void set_trump(int trump) {
    if (trump != trump_ && options_.memo) std::fill(table_.begin(), table_.end(), Entry{});
    trump_ = trump;
  }

  // Can North-South take at least `target` tricks from here, counting the trick in progress?
  bool ns_reaches(Holding holding, int leader, const std::vector<Play>& trick, int target) {
    std::array<Play, 4> plays{};
    std::copy(trick.begin(), trick.end(), plays.begin());
    return reach(holding, leader, plays, static_cast<int>(trick.size()), target);
  }

  // Tricks North-South take from here with best play, counting the trick in progress.
  int ns_value(const Holding& holding, int leader, const std::vector<Play>& trick) {
    int low = 0;
    int high = tricks_left(holding, leader, static_cast<int>(trick.size()));
    if (trick.size() == 4) high += 1;
    while (low < high) {
      int middle = (low + high + 1) / 2;
      if (ns_reaches(holding, leader, trick, middle)) low = middle;
      else high = middle - 1;
    }
    return low;
  }

  // Tricks the side to move takes after it plays this card, counting the trick in progress.
  int value_after_card(const Holding& holding, int leader, std::vector<Play> trick, int suit, int rank) {
    int seat = (leader + static_cast<int>(trick.size())) % 4;
    int total = tricks_left(holding, leader, static_cast<int>(trick.size()));
    Holding after = holding;
    after[seat][suit] &= static_cast<uint16_t>(~(1 << rank));
    trick.push_back({seat, suit, rank});
    int ns = ns_value(after, leader, trick);
    return (seat & 1) == 0 ? ns : total - ns;
  }

  uint64_t nodes() const { return nodes_; }

 private:
  struct Key {
    uint64_t part[4] = {0, 0, 0, 0};
    bool operator==(const Key& other) const {
      return part[0] == other.part[0] && part[1] == other.part[1] && part[2] == other.part[2] &&
             part[3] == other.part[3];
    }
  };
  struct Entry {
    Key key;
    int8_t lower = -1;  // -1 marks an empty slot
    int8_t upper = 0;
  };
  struct Move {
    int suit, rank, score;
  };

  static int hand_size(const Holding& h, int seat) {
    return __builtin_popcount(h[seat][0]) + __builtin_popcount(h[seat][1]) +
           __builtin_popcount(h[seat][2]) + __builtin_popcount(h[seat][3]);
  }

  // Tricks left, counting one in progress. A full trick is not counted: it is resolved first.
  static int tricks_left(const Holding& h, int leader, int played) {
    return played == 4 ? hand_size(h, leader) : hand_size(h, (leader + played) % 4);
  }

  bool beats(const Play& a, const Play& best) const {
    if (a.suit == best.suit) return a.rank > best.rank;
    return a.suit == trump_;
  }

  Key make_key(const Holding& h, int leader) const {
    Holding canon = h;
    if (options_.merge) {
      canon = Holding{};
      for (int suit = 0; suit < 4; suit++) {
        int below = 0;
        for (int rank = 2; rank <= 14; rank++) {
          bool found = false;
          for (int seat = 0; seat < 4; seat++)
            if (h[seat][suit] >> rank & 1) {
              canon[seat][suit] |= static_cast<uint16_t>(1 << below);
              found = true;
            }
          below += found;
        }
      }
    }
    Key key;
    for (int seat = 0; seat < 4; seat++) {
      key.part[seat] = static_cast<uint64_t>(canon[seat][0]) | static_cast<uint64_t>(canon[seat][1]) << 16 |
                       static_cast<uint64_t>(canon[seat][2]) << 32 | static_cast<uint64_t>(canon[seat][3]) << 48;
    }
    key.part[0] ^= static_cast<uint64_t>(leader) << 62;  // ranks never use the top bits
    return key;
  }

  size_t slot_of(const Key& key) const {
    uint64_t x = key.part[0] * 0x9E3779B97F4A7C15ULL;
    x = (x ^ key.part[1]) * 0xC2B2AE3D27D4EB4FULL;
    x = (x ^ key.part[2]) * 0x165667B19E3779F9ULL;
    x = (x ^ key.part[3]) * 0x9E3779B97F4A7C15ULL;
    return static_cast<size_t>(x >> (64 - options_.table_bits));
  }

  std::vector<Move> moves_for(const Holding& h, int seat, const std::array<Play, 4>& trick, int played) const {
    std::vector<Move> moves;
    int led = played == 0 ? -1 : trick[0].suit;
    bool follows = led >= 0 && h[seat][led] != 0;

    uint16_t present[4] = {0, 0, 0, 0};
    for (int s = 0; s < 4; s++)
      for (int d = 0; d < 4; d++) present[d] |= h[s][d];
    for (int i = 0; i < played; i++) present[trick[i].suit] |= static_cast<uint16_t>(1 << trick[i].rank);

    Play best{};
    if (played > 0) {
      best = trick[0];
      for (int i = 1; i < played; i++)
        if (beats(trick[i], best)) best = trick[i];
    }

    for (int suit = 0; suit < 4; suit++) {
      if (follows && suit != led) continue;
      bool previous_mine = false;
      bool is_top = true;
      for (int rank = 14; rank >= 2; rank--) {
        if (!(present[suit] >> rank & 1)) continue;
        bool mine = h[seat][suit] >> rank & 1;
        if (mine && !(options_.touching && previous_mine)) {
          int score = -rank;
          if (options_.ordering) {
            if (played == 0) {
              score = (is_top ? 100 : 0) + (suit == trump_ ? 10 : 0) - rank;
            } else if ((best.seat & 1) == (seat & 1)) {
              score = -rank;  // partner is winning: play low
            } else if (beats({seat, suit, rank}, best)) {
              score = 100 - rank;  // win as cheaply as possible
            } else {
              score = -rank - (suit == trump_ ? 20 : 0);
            }
          }
          moves.push_back({suit, rank, score});
        }
        previous_mine = mine;
        is_top = false;
      }
    }
    if (options_.ordering) {
      std::stable_sort(moves.begin(), moves.end(), [](const Move& a, const Move& b) { return a.score > b.score; });
    }
    return moves;
  }

  bool reach(Holding& h, int leader, std::array<Play, 4>& trick, int played, int target) {
    if (played == 4) {
      Play best = trick[0];
      for (int i = 1; i < 4; i++)
        if (beats(trick[i], best)) best = trick[i];
      std::array<Play, 4> next{};
      return reach(h, best.seat, next, 0, target - ((best.seat & 1) == 0 ? 1 : 0));
    }
    if (target <= 0) return true;
    int seat = (leader + played) % 4;
    int left = hand_size(h, seat);
    if (target > left) return false;
    nodes_++;

    Entry* entry = nullptr;
    Key key;
    if (played == 0 && options_.memo) {
      key = make_key(h, leader);
      entry = &table_[slot_of(key)];
      if (entry->lower >= 0 && entry->key == key) {
        if (entry->lower >= target) return true;
        if (entry->upper < target) return false;
      }
    }

    bool ns_turn = (seat & 1) == 0;
    bool result = !ns_turn;
    for (const Move& m : moves_for(h, seat, trick, played)) {
      h[seat][m.suit] &= static_cast<uint16_t>(~(1 << m.rank));
      trick[played] = {seat, m.suit, m.rank};
      bool r = reach(h, leader, trick, played + 1, target);
      h[seat][m.suit] |= static_cast<uint16_t>(1 << m.rank);
      if (r == ns_turn) {
        result = r;
        break;
      }
    }

    if (entry != nullptr) {
      if (entry->lower < 0 || !(entry->key == key)) {
        entry->key = key;
        entry->lower = 0;
        entry->upper = static_cast<int8_t>(left);
      }
      if (result) entry->lower = std::max<int8_t>(entry->lower, static_cast<int8_t>(target));
      else entry->upper = std::min<int8_t>(entry->upper, static_cast<int8_t>(target - 1));
    }
    return result;
  }

  Options options_;
  int trump_ = -1;
  std::vector<Entry> table_;
  uint64_t nodes_ = 0;
};

}  // namespace altsolve
