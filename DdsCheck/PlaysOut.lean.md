# Reviewing `PlaysOut.lean`

This is a guide to [PlaysOut.lean](PlaysOut.lean). `nsTricks` in [Rules.lean](Rules.lean) stops after 52
cards. This file proves that's exactly when a game on a valid deal ends, so the limit never cuts a game
short and nobody gets stuck.

**What to read:** the two pieces below, `afterPlay` and `valid_deal_plays_out`.

**What to skip:** everything else in the file, including `Balanced` and all the proofs. Lean has checked
them.

The code blocks are copied exactly from the file. See [Strategy.lean.md](Strategy.lean.md) for the
notation, and for `IsLine`.

## The position after a line (line 135)

```lean
def afterPlay (strain : Strain) : State → List Card → State
  | s, [] => s
  | s, c :: cards => afterPlay strain (step strain s c).1 cards
```

This plays a list of cards in order, and gives the final position.

**Check:** this just applies `step` to each card in turn.

## The theorem (line 199)

```lean
theorem valid_deal_plays_out (strain : Strain) {h : Hands} (hv : validDeal h) (leader : Seat)
    (cards : List Card) (hl : IsLine strain 52 (start h leader) cards) :
    cards.length = 52 ∧ (afterPlay strain (start h leader) cards).trick = [] ∧
      ∀ x, (afterPlay strain (start h leader) cards).hands.get x = [] := by
```

The requirements are:
- `hv`: the deal is valid.
- `hl`: `cards` is a complete line of play from the opening lead, for any strain and any leader.

It then says three things hold:
1. **`cards.length = 52`:** every complete line has exactly 52 cards. Since `IsLine` allows a line to stop
   early only when someone has no legal card, this means nobody ever gets stuck.
2. **`.trick = []`:** at the end, the table is clear, so there's no unfinished trick.
3. **`∀ x, ... = []`:** at the end, every hand is empty.

**Check:** these are what you need for "52 plays is the whole game".

## How the proof works, if you're curious

You don't need this for the review. It's an induction on the cards left, following `Balanced`, which
tracks hand sizes during a trick: the player to move holds `L` cards, and anyone who has already played to
this trick holds `L - 1`. Each legal card keeps that pattern. A finished trick leaves all four hands at
`L - 1`, whoever won it.

## What it doesn't state

- **Exactly 13 tricks:** that follows from 52 cards and four to a trick, but no theorem says it directly.
  `declarerTricks` in [Par.lean](Par.lean) relies on East-West's tricks being "the rest of the 13". The
  file [Checker.lean](Checker.lean) has proved a related bound, that North-South can't take more than 13,
  but nothing here counts East-West's tricks separately and shows the two add up to 13.
- **Each card played once:** this also follows, but isn't stated separately.

These don't affect North-South's trick counts, which are what the generated theorems state.

## Checklist

- [ ] **`afterPlay`** applies `step` in order
- [ ] **`valid_deal_plays_out`** says what you need about the length of a game
