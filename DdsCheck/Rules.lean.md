# Reviewing `Rules.lean`

This is a line-by-line guide to [Rules.lean](Rules.lean). Every theorem in the project is about the
definitions in that file, so a mistake there would give correct proofs about the wrong game.

You don't need to know Lean to review it. Section 1 covers the notation, and section 2 goes through
each definition, with a **Check** line saying what to confirm. Section 3 lists what the file
deliberately leaves out, and section 4 is a checklist.

The examples here have all been checked by Lean. The code blocks are copied exactly from the file.

## 1. Reading the notation

| Lean | Meaning |
|---|---|
| `def f (x : A) : B := ...` | Defines function `f`, taking an `x` of type `A` and returning a `B` |
| `f x y` | Calls `f` on `x` and `y`. Lean uses spaces, not `f(x, y)` |
| `/-- text -/` | A comment describing the next definition. Lean ignores what it says |
| `inductive T \| a \| b` | A type whose only values are `a` and `b` |
| `structure T where` | A record with named fields, like a row in a table |
| `.north` | Short for `Seat.north`; Lean works out the type from context |
| `A → B` | A function from `A` to `B` |
| `A × B` | A pair. For `p : A × B`, `p.1` is the first part and `p.2` the second |
| `Nat` | A whole number, 0 or more |
| `List A`, `[a, b]`, `[]` | A list, a list of two items, and the empty list |
| `x :: xs` | A list with first item `x` and the rest `xs` |
| `xs ++ ys` | The two lists joined |
| `Option A` | Either `some x` or `none`, meaning "maybe an `A`" |
| `let x := ...` | Names a value for use in the following lines |
| `match x with \| p => ...` | Tries the patterns in order and uses the first that fits. `_` fits anything |
| `fun x => ...` | A function with no name |
| `(· != c)` | Short for `fun x => x != c`. `·` stands for the input |
| `==`, `!=` | Equal and not equal, giving `true` or `false` |
| `∧`, `≤` | And, less than or equal |
| `{ h with north := v }` | A copy of record `h` with `north` replaced by `v` |
| `deriving DecidableEq, Repr, Inhabited` | Asks Lean to generate equality testing, printing and a default value. It has no effect on the rules, so you can ignore it |
| `namespace Bridge` ... `end Bridge` | Groups the names, so `value` is really `Bridge.value` |

Three list functions come up often:
- `l.filter p` keeps the items where `p` is true.
- `l.map f` applies `f` to every item.
- `l.foldl f x` starts with `x` and combines it with each item in turn, from first to last.

## 2. The definitions

### Suits and strains (lines 11–15)

```lean
inductive Suit | spades | hearts | diamonds | clubs
  deriving DecidableEq, Repr, Inhabited
```

```lean
abbrev Strain := Option Suit
```

There are exactly four suits. A strain is `some` suit, which makes it the trump suit, or `none`,
which is notrump. The order of the suits has no effect on play: nothing here ranks one suit above
another.

**Check:** the four suits are right, and `none` means notrump.

### Cards (lines 18–21)

```lean
structure Card where
  suit : Suit
  rank : Nat
  deriving DecidableEq, Repr, Inhabited
```

A card is a suit and a number. Higher numbers are stronger. `validDeal` below limits a real deal to
ranks 2–14, so **14 = ace, 13 = king, 12 = queen, 11 = jack, 10 = ten**.

The ♠A is written `⟨.spades, 14⟩`.

**Check:** a higher rank means a stronger card.

### Seats and clockwise order (lines 23–28)

```lean
inductive Seat | north | east | south | west
  deriving DecidableEq, Repr, Inhabited
```

```lean
def Seat.next : Seat → Seat
  | .north => .east | .east => .south | .south => .west | .west => .north
```

`Seat.next` gives the next player clockwise. Each `|` is one case, so this reads: after North comes
East, after East comes South, after South comes West, after West comes North.

**Check:** this is clockwise order.

### Partnerships (lines 30–35)

```lean
inductive Side | ns | ew
  deriving DecidableEq, Repr, Inhabited
```

```lean
def Seat.side : Seat → Side
  | .north | .south => .ns
  | .east | .west => .ew
```

North and South are one side, and East and West the other. Writing `.north | .south` gives one
answer for both seats.

**Check:** the partnerships are right.

### Hands (lines 37–45)

```lean
structure Hands where
  north : List Card
  east : List Card
  south : List Card
  west : List Card
  deriving DecidableEq, Repr, Inhabited
```

```lean
def Hands.get (h : Hands) : Seat → List Card
  | .north => h.north | .east => h.east | .south => h.south | .west => h.west
```

`Hands` holds the four hands. `h.get seat` looks up one seat's hand.

**Check:** each seat gets its own hand, with none mixed up.

### Removing a played card (lines 48–54)

```lean
def Hands.remove (h : Hands) (seat : Seat) (c : Card) : Hands :=
  let out := fun (l : List Card) => l.filter (· != c)
  match seat with
  | .north => { h with north := out h.north }
  | .east => { h with east := out h.east }
  | .south => { h with south := out h.south }
  | .west => { h with west := out h.west }
```

`out` keeps every card that isn't `c`. The `match` applies it to the hand of the seat that played,
and the other three hands are copied unchanged.

**Check:** the card leaves only the hand of the player who played it.

### The position (lines 56–62)

```lean
structure State where
  hands : Hands
  /-- Cards played to the current trick, in the order played. -/
  trick : List (Seat × Card)
  /-- Whose turn it is to play. -/
  turn : Seat
  deriving DecidableEq, Repr, Inhabited
```

A position has three parts: the cards still in hand, the cards on the table with who played each,
and whose turn it is. **The first item in `trick` is the card that was led.**

Tricks won so far aren't stored. `value` adds up tricks from here on.

**Check:** this is everything needed to continue play. In double-dummy play it is, because all cards
are visible and the past doesn't matter.

### Following suit (lines 65–71)

```lean
def legal (s : State) : List Card :=
  let hand := s.hands.get s.turn
  match s.trick with
  | [] => hand
  | (_, led) :: _ =>
    let following := hand.filter (·.suit == led.suit)
    if following.isEmpty then hand else following
```

Line by line:
- `hand` is the hand of the player whose turn it is.
- `| [] => hand`: if the table is empty, this player is on lead and may play anything.
- `| (_, led) :: _`: otherwise, `led` is the first card on the table. The `_`s ignore who led it and
  the later cards.
- `following` is this player's cards in the suit led.
- If they hold none, they may play anything. Otherwise they must play one of those.

**Example:** holding ♠A and ♥K, with ♠2 led, the only legal card is ♠A. With ♦2 led, both are legal.

**Check:** this is the rule for following suit. It follows the suit **led**, not the suit currently
winning, because it reads the first card on the table.

### Which card takes over (lines 75–77)

```lean
def beats (strain : Strain) (a best : Card) : Bool :=
  if a.suit == best.suit then decide (best.rank < a.rank)
  else strain == some a.suit
```

`best` is the card currently winning the trick, and `a` is a new card. Does `a` take over?
- **Same suit:** yes, if `a` ranks higher. `decide` just turns the comparison into `true` or `false`.
- **Different suit:** yes, only if `a` is a trump (`strain == some a.suit`).

Going through the different-suit cases, since this is where a mistake would hide:

| `best` is | `a` is | `a` takes over? | Why |
|---|---|---|---|
| Not a trump | A trump | Yes | A ruff |
| Not a trump | Another non-trump | No | A discard |
| A trump | Not a trump | No | `a` isn't a trump |
| Any card, in notrump | Another suit | No | With strain `none`, nothing equals `some a.suit` |

Two trumps are the same suit, so an overruff is decided by rank on the first line.

**Check:** this covers all those cases correctly.

### Who wins the trick (lines 80–82)

```lean
def trickWinner (strain : Strain) (first : Seat × Card) (rest : List (Seat × Card)) :
    Seat × Card :=
  rest.foldl (fun best p => if beats strain p.2 best.2 then p else best) first
```

This starts with the first card as `best` and goes through the other plays in order, replacing `best`
whenever a play beats it. `p.2` and `best.2` are the cards, and `.1` would be the seats.

Because `best` starts as the card led, a discard can't win and the led suit matters without being
mentioned here.

**Example:** with spades as trumps, if North leads ♥A, East plays ♥2, South ruffs with ♠2 and West
overruffs with ♠3, then West wins.

**Check:** one pass through the plays finds the right winner. The proved theorems
`winner_highest_trump` and `winner_highest_of_suit_led` in [RulesProps.lean](RulesProps.lean) confirm
this for every trick.

### Playing a card (lines 86–93)

```lean
def step (strain : Strain) (s : State) (c : Card) : State × Option Seat :=
  let hands := s.hands.remove s.turn c
  let trick := s.trick ++ [(s.turn, c)]
  match trick with
  | [p₁, p₂, p₃, p₄] =>
    let w := (trickWinner strain p₁ [p₂, p₃, p₄]).1
    ({ hands, trick := [], turn := w }, some w)
  | _ => ({ hands, trick, turn := s.turn.next }, none)
```

This returns two things: the next position, and the winning seat if this card finished a trick.

- `hands`: the card leaves the player's hand.
- `trick`: the card goes at the end of the table, so the led card stays first.
- `[p₁, p₂, p₃, p₄]`: if that makes four plays, find the winner. `.1` takes the seat from the winning
  play. The next position has an empty table, with the winner to play, and it reports `some w`.
- `_`: otherwise the trick continues. Play passes clockwise, and it reports `none`.

`{ hands, trick := [], turn := w }` is a new `State`. Writing just `hands` means `hands := hands`.

`step` doesn't check that the card is legal. That's `legal`'s job, because `value` below only ever
tries legal cards.

**Check:** the winner of a trick leads to the next one, and otherwise play passes clockwise.

### Counting a trick (lines 96–98)

```lean
def nsPoint : Option Seat → Nat
  | some w => if w.side = .ns then 1 else 0
  | none => 0
```

This takes the second result of `step`. North-South score 1 when one of them wins a trick, and 0
when East-West win one or the trick isn't finished. East-West's tricks aren't counted separately.

**Check:** a trick counts for the partnership of the player who won it.

### Largest and smallest (lines 100–107)

```lean
def maxOf : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxOf xs)
```

```lean
def minOf : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: ys => min x (minOf (y :: ys))
```

These find the largest and smallest numbers in a list, by comparing the first with the answer for the
rest. Both give 0 for an empty list, which `valid_deal_plays_out` shows doesn't arise while cards remain.

`minOf` has the extra `[x]` case because otherwise the empty list's 0 would be included in every
minimum and the answer would always be 0. `maxOf` doesn't need it, since 0 can't raise a maximum of
whole numbers.

**Example:** `maxOf [1, 3, 2]` is 3, and `minOf [1, 3, 2]` is 1.

**Check:** these are the ordinary largest and smallest.

### The double-dummy value (lines 112–120)

This is the most important definition in the file.

```lean
def value (strain : Strain) : (fuel : Nat) → State → Nat
  | 0, _ => 0
  | fuel + 1, s =>
    let outcomes := (legal s).map fun c =>
      let r := step strain s c
      nsPoint r.2 + value strain fuel r.1
    match s.turn.side with
    | .ns => maxOf outcomes
    | .ew => minOf outcomes
```

`value` gives the tricks North-South take from this position on, with best play by both sides. It
calls itself with one less card to play:

- **`fuel`** is how many cards are left to play. With 0 left, North-South take no more tricks.
- **`outcomes`** tries each legal card `c`. `r` is the result of playing it, so each outcome is "the
  point for this card, plus the value of the position after it" (`r.2` is the possible winner and
  `r.1` the next position).
- **The `match`** decides whose choice it is. North-South choose the largest outcome and East-West the
  smallest, because East-West want North-South to take as few as possible.

Both hands of a partnership are played by the same "mind" with all cards visible, which is what makes
this double dummy. It tries every line of play. That's far too slow to run on a full deal, so the
certificates exist to prove its answer without running it.

**Example, a finesse:** South holds ♠2 3, North ♠A Q, West ♠K 4 and East ♣A K, with South on lead in
notrump. Whatever West plays, North plays just high enough, so North-South take 2. Swap the East and
West hands, so the king sits behind the ace-queen, and they take only 1.

**Check:** North-South maximize, East-West minimize, and every outcome adds this card's point to the
value of what follows. The theorem `nsTricks_eq_iff` in [Strategy.lean](Strategy.lean) proves this
matches what each side can guarantee with a strategy, so swapping max and min would make it false.

### All the cards (line 122)

```lean
def Hands.cards (h : Hands) : List Card := h.north ++ h.east ++ h.south ++ h.west
```

The four hands joined into one list.

### A valid deal (lines 125–127)

```lean
def validDeal (h : Hands) : Prop :=
  h.north.length = 13 ∧ h.east.length = 13 ∧ h.south.length = 13 ∧ h.west.length = 13 ∧
  h.cards.Nodup ∧ h.cards.all (fun c => decide (2 ≤ c.rank ∧ c.rank ≤ 14)) = true
```

`Prop` means this is a statement that's either true or false, not a calculation. It says:
- Each hand has 13 cards.
- `Nodup`: no card appears twice ("no duplicates").
- Every rank is from 2 to 14.

It never says "all 52 cards appear", but that follows. With four suits and 13 ranks there are exactly
52 possible cards, so 52 different cards must be all of them.

**Check:** this describes a deal, and the counting argument convinces you.

### The start of play (line 130)

```lean
def start (h : Hands) (leader : Seat) : State := { hands := h, trick := [], turn := leader }
```

The opening position: all the hands, an empty table, and the opening leader to play.

**Check:** nothing else needs setting up.

### The final quantity (lines 133–134)

```lean
def nsTricks (strain : Strain) (h : Hands) (leader : Seat) : Nat :=
  value strain 52 (start h leader)
```

This is what the generated theorems are about: North-South's tricks from the opening lead, with 52
cards to play. `valid_deal_plays_out` in [PlaysOut.lean](PlaysOut.lean) proves that on a valid deal
every line uses exactly 52 cards, so the limit never cuts a game short.

**Check:** this is the question you want answered.

## 3. What the file leaves out

These are deliberate, and don't indicate a gap:

| Not in the file | Why |
|---|---|
| Declarer and dummy | Only the opening leader matters here, since all four hands are visible and each side chooses its best cards. [Par.lean](Par.lean) handles declarers: the leader sits to declarer's left |
| Bidding, contracts and scores | These are in [Par.lean](Par.lean). This file only counts tricks |
| East-West's tricks | They're the rest of the 13, so counting one side is enough |
| Revokes, claims and other irregularities | Only legal play is modelled |
| Card names such as ace or king | Ranks are just numbers, and only their order matters. `value_canon` in [Canon.lean](Canon.lean) proves that |

## 4. Checklist

- [ ] **Clockwise order and partnerships:** `Seat.next`, `Seat.side`
- [ ] **Following suit:** `legal` uses the suit led, and a void player may play anything
- [ ] **Beating a card:** `beats`, all cases in its table
- [ ] **Winning a trick:** `trickWinner` starts from the card led
- [ ] **Playing a card:** `step`, removing the card, and the winner leading next
- [ ] **Scoring tricks:** `nsPoint` counts North-South's tricks
- [ ] **Optimal play:** `value`, with North-South maximizing and East-West minimizing
- [ ] **A deal:** `validDeal`, and the argument that 52 different cards means all of them
- [ ] **The question:** `start` and `nsTricks`

As a cross-check, the Part 2 theorems in [RulesProps.lean](RulesProps.lean) state the same rules in
plainer terms, each proved for every position.
