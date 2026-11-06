# Reviewing `RulesProps.lean`

This is a guide to [RulesProps.lean](RulesProps.lean). It restates the rules from
[Rules.lean](Rules.lean) as plain statements, each proved for **every** position. So it's a second way
to check those rules: instead of reading how the code works, you read what it does.

**What to read:** the statements below.

**What to skip:** all the proofs, and the helper theorems and `WinnerInv`, which this guide leaves out.
Lean has checked them.

Since Lean has proved each statement, the only question is whether it's the right rule of bridge.

The code blocks are copied exactly from the file. See [Rules.lean.md](Rules.lean.md) and
[Strategy.lean.md](Strategy.lean.md) for the notation. Here, `{s : State}` means the same as
`(s : State)`, except that Lean works out `s` itself when the theorem is used. And a condition such as
`(h : s.trick = [])` is a requirement: the theorem applies when it holds.

## Part 1: every rule error comes down to a single move

### The induction (line 45)

```lean
theorem minimax_eq_value (strain : Strain) (R : AltRules) (s : State)
    (hlegal : ∀ t, Reachable strain s t → R.legal t = legal t)
    (hstep : ∀ t c, Reachable strain s t → c ∈ legal t → R.step t c = step strain t c)
    (n : Nat) : minimax R n s = value strain n s := by
```

`R` is any other version of the rules. If it agrees with `legal` and `step` on every position reachable
from `s`, it gives the same value from `s`, however many cards are left.

So everything about the rules comes down to `legal` and `step`, which is what Part 2 pins down. The
definitions it uses are on lines 22–41:
- **`AltRules`:** a candidate `legal` and `step`.
- **`minimax`:** the same calculation as `value`, using those candidates.
- **`Reachable`:** positions that can arise from `s` by legal play.

**Limit:** `minimax` is copied from `value`, including its maximizing, minimizing and `nsPoint`. So this
theorem says nothing about those parts. The max and min are covered by [Strategy.lean](Strategy.lean),
and you'd check `nsPoint` by reading it.

**Check:** you accept that rules agreeing move by move must agree overall.

## Part 2: legal plays

### Only your own cards (line 71)

```lean
theorem legal_mem_hand (s : State) {c : Card} (h : c ∈ legal s) : c ∈ s.hands.get s.turn := by
```

Any legal card comes from the hand of the player whose turn it is.

### Leading (line 81)

```lean
theorem legal_lead {s : State} (h : s.trick = []) : legal s = s.hands.get s.turn := by
```

If the table is empty, every card in the hand is legal.

### Following suit (line 85)

```lean
theorem legal_follow {s : State} {first : Seat × Card} {rest : List (Seat × Card)}
    (h : s.trick = first :: rest)
    (holds : ∃ x ∈ s.hands.get s.turn, x.suit = first.2.suit) (c : Card) :
    c ∈ legal s ↔ c ∈ s.hands.get s.turn ∧ c.suit = first.2.suit := by
```

`first` is the first card on the table. If you hold a card of its suit, then a card is legal exactly when
it's in your hand and in that suit.

### Void in the suit led (line 102)

```lean
theorem legal_void {s : State} {first : Seat × Card} {rest : List (Seat × Card)}
    (h : s.trick = first :: rest)
    (void : ∀ x ∈ s.hands.get s.turn, x.suit ≠ first.2.suit) :
    legal s = s.hands.get s.turn := by
```

If none of your cards is in the suit led, every card in your hand is legal.

**Check:** these four are the complete rule, since every position is either a lead, or holding the suit
led, or void in it.

## Part 2: playing a card

### The played card goes (line 131)

```lean
theorem play_removes_card (strain : Strain) (s : State) (c x : Card) :
    x ∈ (step strain s c).1.hands.get s.turn ↔ x ∈ s.hands.get s.turn ∧ x ≠ c := by
```

After playing `c`, your hand holds exactly the cards it held before, apart from `c`.

### The other hands stay (line 136)

```lean
theorem play_keeps_other_hands (strain : Strain) (s : State) (c : Card) {other : Seat}
    (hne : other ≠ s.turn) : (step strain s c).1.hands.get other = s.hands.get other := by
```

Any other player's hand doesn't change.

### Before the fourth card (line 141)

```lean
theorem step_continue (strain : Strain) (s : State) (c : Card) (h : s.trick.length < 3) :
    (step strain s c).1.trick = s.trick ++ [(s.turn, c)] ∧
      (step strain s c).1.turn = s.turn.next ∧ (step strain s c).2 = none := by
```

With fewer than three cards on the table, the card joins the end of the trick, play passes clockwise, and
no trick is won.

### The fourth card (line 151)

```lean
theorem step_complete (strain : Strain) (s : State) (c : Card) {p₁ p₂ p₃ : Seat × Card}
    (h : s.trick = [p₁, p₂, p₃]) :
    let w := (trickWinner strain p₁ [p₂, p₃, (s.turn, c)]).1
    (step strain s c).1.trick = [] ∧ (step strain s c).1.turn = w ∧ (step strain s c).2 = some w := by
```

With three cards on the table, your card finishes the trick. `w` is the winning seat. The table clears,
`w` plays next, and `w` is reported as the winner.

### Scoring a trick (lines 158–161)

```lean
theorem nsPoint_some (w : Seat) : nsPoint (some w) = if w.side = .ns then 1 else 0 := rfl
```

```lean
theorem nsPoint_none : nsPoint none = 0 := rfl
```

North-South score 1 for a trick one of them wins, and 0 for anything else.

**These add little:** `rfl` means they're true just by reading the definition, so they restate `nsPoint`
rather than give independent evidence. Reading `nsPoint` in [Rules.lean](Rules.lean) is what matters.

### Partnerships and clockwise order (lines 164–169)

```lean
theorem partners : Seat.north.side = Seat.south.side ∧ Seat.east.side = Seat.west.side ∧
    Seat.north.side ≠ Seat.east.side := by decide
```

```lean
theorem clockwise : Seat.north.next = .east ∧ Seat.east.next = .south ∧
    Seat.south.next = .west ∧ Seat.west.next = .north := by decide
```

North and South are partners, East and West are partners, and the two sides differ. Clockwise order is
North, East, South, West, back to North.

**Check:** the card leaves one hand only, the winner leads next, and otherwise play passes clockwise.

## Part 2: who wins a trick

### The winner played in the trick (line 307)

```lean
theorem winner_mem (strain : Strain) (first : Seat × Card) (rest : List (Seat × Card)) :
    trickWinner strain first rest ∈ first :: rest :=
```

The winning play is one of the plays in the trick.

### With a trump played (line 312)

```lean
theorem winner_highest_trump {strain : Strain} {first : Seat × Card} {rest : List (Seat × Card)}
    (h : ∃ p ∈ first :: rest, strain = some p.2.suit) :
    strain = some (trickWinner strain first rest).2.suit ∧
      ∀ p ∈ first :: rest, strain = some p.2.suit →
        p.2.rank ≤ (trickWinner strain first rest).2.rank :=
```

If any card in the trick is a trump, the winner is a trump, and no trump in the trick outranks it.

### With no trump played (line 320)

```lean
theorem winner_highest_of_suit_led {strain : Strain} {first : Seat × Card}
    {rest : List (Seat × Card)} (h : ∀ p ∈ first :: rest, strain ≠ some p.2.suit) :
    (trickWinner strain first rest).2.suit = first.2.suit ∧
      ∀ p ∈ first :: rest, p.2.suit = first.2.suit →
        p.2.rank ≤ (trickWinner strain first rest).2.rank :=
```

If no card in the trick is a trump, the winner is in the suit led, and no card of that suit in the trick
outranks it.

### In notrump (line 328)

```lean
theorem winner_notrump (first : Seat × Card) (rest : List (Seat × Card)) :
    (trickWinner none first rest).2.suit = first.2.suit ∧
      ∀ p ∈ first :: rest, p.2.suit = first.2.suit →
        p.2.rank ≤ (trickWinner none first rest).2.rank :=
```

In notrump, the winner is the highest card of the suit led.

**Worth knowing:** "no card outranks it" fixes the winner only if no card appears twice. A valid deal
guarantees that through `validDeal`.

**Check:** these state the rule for winning a trick. They cover every case, since a trick either has a
trump in it or doesn't.

## Checklist

- [ ] **Induction:** `minimax_eq_value` is a fair statement of "only `legal` and `step` matter"
- [ ] **Following suit:** `legal_lead`, `legal_follow`, `legal_void`
- [ ] **Playing a card:** `play_removes_card`, `play_keeps_other_hands`
- [ ] **Turn order:** `step_continue`, `step_complete`
- [ ] **Seats:** `partners`, `clockwise`
- [ ] **Winning a trick:** `winner_highest_trump`, `winner_highest_of_suit_led`, `winner_notrump`
