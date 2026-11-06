# Reviewing `Strategy.lean`

This is a guide to [Strategy.lean](Strategy.lean). `value` in [Rules.lean](Rules.lean) defines perfect
play with `maxOf` and `minOf`. This file says what that's supposed to mean in a bridge player's terms,
and proves the two agree.

**What to read:** the definitions on lines 20–55, and the theorem statements on lines 271–306.

**What to skip:** everything between them, and all the proofs. Lean has checked those. So in this guide
you're only judging whether the statements say what you mean.

The examples have been checked by Lean, and the code blocks are copied exactly from the file. See
[Rules.lean.md](Rules.lean.md) for the basic notation.

## 1. Extra notation

| Lean | Meaning |
|---|---|
| `theorem name (...) : statement := by` | Lean has proved `statement`. What follows `:= by` is the proof, which you can skip |
| `Prop` | A statement that's true or false |
| `∃ x, P` | There exists an `x` with `P` |
| `∀ x, P` | For every `x`, `P` holds |
| `P → Q` | If `P` then `Q` |
| `P ↔ Q` | `P` and `Q` are true in exactly the same cases |
| `c ∈ l` | `c` is in list `l` |
| `≠` | Not equal |
| `σ` | A Greek letter used here as a name for a strategy |
| `σ.Valid` | Short for `Strategy.Valid σ` |

## 2. The definitions

### A complete line of play (lines 20–23)

```lean
def IsLine (strain : Strain) : Nat → State → List Card → Prop
  | 0, _, cards => cards = []
  | _ + 1, s, [] => legal s = []
  | n + 1, s, c :: cards => c ∈ legal s ∧ IsLine strain n (step strain s c).1 cards
```

This says a list of cards is one complete way the play could go from position `s`, with up to `n` cards
left to play. The three cases are:
- **No cards left to play:** the list must be empty.
- **The list has ended early:** that's allowed only if the player to move has no legal card, so a line
  can't simply stop.
- **Otherwise:** the first card must be legal, and the rest must be a line from the position it leads to.

[PlaysOut.lean](PlaysOut.lean) proves that on a valid deal the early stop never happens.

**Check:** this describes playing legal cards until the end, with no skipping.

### Counting tricks along a line (lines 26–28)

```lean
def tricksOf (strain : Strain) : State → List Card → Nat
  | _, [] => 0
  | s, c :: cards => nsPoint (step strain s c).2 + tricksOf strain (step strain s c).1 cards
```

This plays the cards in order, and adds up North-South's tricks.

**Check:** this is a plain count. It uses `nsPoint`, so a mistake in that would pass unnoticed here,
which is why `nsPoint` needs reviewing itself in [Rules.lean](Rules.lean).

### Strategies (lines 32–39)

```lean
abbrev Strategy := List Card → State → Card
```

```lean
def Strategy.Valid (σ : Strategy) : Prop :=
  ∀ history s, legal s ≠ [] → σ history s ∈ legal s
```

```lean
def Strategy.after (σ : Strategy) (c : Card) : Strategy := fun history s => σ (c :: history) s
```

- **`Strategy`** chooses a card, given all the cards played so far and the current position. So a
  strategy can depend on the history of the play, which makes the theorems stronger: no strategy of
  any kind can beat `value`.
- **`Valid`** means it always picks a legal card when there is one. Without this, a strategy could
  "guarantee" anything by playing illegally, so that no line ever followed it.
- **`after`** is bookkeeping: the same strategy, with one more card added to the history.

**Check:** a strategy has access to everything a player could use, and has to play legally.

### Following a strategy (lines 42–45)

```lean
def Follows (strain : Strain) (side : Side) : Strategy → State → List Card → Prop
  | _, _, [] => True
  | σ, s, c :: cards =>
    (s.turn.side = side → c = σ [] s) ∧ Follows strain side (σ.after c) (step strain s c).1 cards
```

This says `side` played the strategy's card on each of its own turns in this line. The key part is
`s.turn.side = side → c = σ [] s`: on `side`'s turn the card must be the strategy's choice. On the
other side's turns there's no restriction, so they can play any legal card.

**Check:** this constrains only one side, and leaves the opponents free.

### The two guarantees (lines 48–55)

```lean
def NSCanTake (strain : Strain) (n : Nat) (s : State) (t : Nat) : Prop :=
  ∃ σ : Strategy, σ.Valid ∧ ∀ cards, IsLine strain n s cards → Follows strain .ns σ s cards →
    t ≤ tricksOf strain s cards
```

```lean
def EWCanHold (strain : Strain) (n : Nat) (s : State) (t : Nat) : Prop :=
  ∃ σ : Strategy, σ.Valid ∧ ∀ cards, IsLine strain n s cards → Follows strain .ew σ s cards →
    tricksOf strain s cards ≤ t
```

Read `NSCanTake` as: **there's a legal strategy for North-South such that on every complete line of
play where they follow it, they take at least `t` tricks.** `EWCanHold` is the same for East-West,
holding North-South to at most `t`.

Neither mentions `maxOf`, `minOf` or `value`, which is the point of this file.

**Check:** these are what you mean by "North-South can always make `t`" and "East-West can always hold
them to `t`". **This is the most important check in the file.**

## 3. The theorems

### North-South's guarantee (line 271)

```lean
theorem nsCanTake_iff (strain : Strain) (n : Nat) (s : State) (t : Nat) :
    NSCanTake strain n s t ↔ t ≤ value strain n s := by
```

North-South can guarantee `t` tricks exactly when `t` is at most `value`.

### East-West's guarantee (line 283)

```lean
theorem ewCanHold_iff (strain : Strain) (n : Nat) (s : State) (t : Nat) :
    EWCanHold strain n s t ↔ value strain n s ≤ t := by
```

East-West can hold them to `t` exactly when `value` is at most `t`.

Each `↔` runs both ways, so together they say that `value` is the most North-South can guarantee and the
least East-West can hold them to.

### The value (line 295)

```lean
theorem value_eq_iff (strain : Strain) (n : Nat) (s : State) (k : Nat) :
    value strain n s = k ↔ NSCanTake strain n s k ∧ EWCanHold strain n s k := by
```

`value` is `k` exactly when both sides can guarantee `k`.

### What a generated theorem means (line 303)

```lean
theorem nsTricks_eq_iff (strain : Strain) (h : Hands) (leader : Seat) (k : Nat) :
    nsTricks strain h leader = k ↔
      NSCanTake strain 52 (start h leader) k ∧ EWCanHold strain 52 (start h leader) k :=
```

This is the same for a whole deal. It means a generated theorem such as
`nsTricks (some .spades) deal .east = 5` says:
- North-South have a strategy that takes at least 5 against every defence.
- East-West have a strategy that holds them to at most 5 against every line of play.

**Example, a finesse:** South holds ♠2 3, North ♠A Q, West ♠K 4 and East ♣A K, with South on lead in
notrump. Lean confirms that North-South can guarantee 2 tricks, and that East-West can hold them to 2.

**Check:** you agree that this two-part statement is what "North-South take exactly `k`" means.

### Why a guarantee can't be empty (line 241)

```lean
theorem playout_spec (strain : Strain) (n : Nat) (σ τ : Strategy) (s : State)
    (hσ : σ.Valid) (hτ : τ.Valid) :
    IsLine strain n s (playout strain n σ τ s) ∧
      Follows strain .ns σ s (playout strain n σ τ s) ∧
      Follows strain .ew τ s (playout strain n σ τ s) := by
```

`NSCanTake` says "on every line that follows the strategy". If no such line existed, that would be true
of anything. This theorem rules that out: any two valid strategies (`σ` for North-South and `τ` for
East-West) produce a complete line following both.

**Check:** nothing more is needed here; it's only to show the guarantees mean something.

## 4. What this file does and doesn't settle

- **It settles:** `value` has its maximizing and minimizing the right way round. If they were swapped,
  these theorems would be false.
- **It doesn't settle:** the rules themselves. `legal`, `step` and `nsPoint` appear in these
  definitions, so those need your review in [Rules.lean](Rules.lean).

## 5. Checklist

- [ ] **Lines of play:** `IsLine` means legal play to the end
- [ ] **Counting:** `tricksOf` adds up North-South's tricks
- [ ] **Strategies:** `Strategy` and `Valid`, with full information and legal cards only
- [ ] **Following:** `Follows` constrains one side only
- [ ] **Guarantees:** `NSCanTake` and `EWCanHold` say what you mean
- [ ] **The result:** `nsTricks_eq_iff` is what you want a generated theorem to mean
