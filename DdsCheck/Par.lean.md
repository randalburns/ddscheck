# Reviewing `Par.lean`

This is a guide to [Par.lean](Par.lean), from the top of the file down to `dealPar` (line 121). Those
lines define duplicate scoring and the game that defines par, so a mistake there would give a correct
proof of the wrong par score. Everything below `dealPar` is a fast way to calculate the same thing,
which Lean has proved equal, so you can skip it.

You'll review two things:
- **Scoring**, which you can check against the rules of duplicate bridge.
- **The par game**, which is a definition, so the question is whether it says what you mean by par.

Section 1 adds to the notation in [Rules.lean.md](Rules.lean.md), which covers the basics. Section 2
goes through each definition, and section 3 is a checklist.

The examples here have all been checked by Lean, and the code blocks are copied exactly from the file.

## 1. Extra notation

| Lean | Meaning |
|---|---|
| `Int` | A whole number that can be negative. Scores use this |
| `(down : Int)` | Treat the `Nat` called `down` as an `Int`, so that subtracting is safe |
| `a - b` on `Nat` | Subtraction that stops at 0: `3 - 5` is 0. Scoring only does this after checking the order |
| `a / 5`, `a % 5` on `Nat` | Whole-number division and remainder: `14 / 5` is 2, and `14 % 5` is 4 |
| `a \|\| b` | Or, on `true` and `false` |
| `if c then x else y` | `x` if `c` holds, otherwise `y` |
| `List.range' a n` | The `n` numbers starting at `a`: `List.range' 3 4` is `[3, 4, 5, 6]` |
| `Strain` | From [Rules.lean](Rules.lean): `some` suit for a trump suit, or `none` for notrump |

## 2. The definitions

### Vulnerability (lines 21–26)

```lean
inductive Vulnerability | none | both | ns | ew
  deriving DecidableEq, Repr, Inhabited
```

```lean
def Vulnerability.of (v : Vulnerability) : Side → Bool
  | .ns => v == .both || v == .ns
  | .ew => v == .both || v == .ew
```

The four vulnerability settings. `v.of side` says whether that side is vulnerable: North-South are if
the setting is `both` or `ns`, and East-West are if it's `both` or `ew`.

**Check:** both lines give the right answer for all four settings.

### Trick values (lines 31–33)

```lean
def perTrick : Strain → Int
  | some .clubs | some .diamonds => 20
  | _ => 30
```

20 points per trick in the minors. `_` covers everything else, which is the majors and notrump, at 30.

**Check:** these are the trick values. The extra 10 for notrump is in the next definition.

### Points for the contract (lines 36–37)

```lean
def contractPoints (level : Nat) (strain : Strain) : Int :=
  level * perTrick strain + if strain = none then 10 else 0
```

The value of the tricks bid: level times the trick value, plus 10 in notrump.

**Examples:** 3NT is 100, 4♠ is 120, 5♣ is 100 and 4♣ is 80.

**Check:** these reach the game threshold of 100 at 3NT, 4 of a major and 5 of a minor.

### Score for making a contract (lines 40–47)

```lean
def madeScore (vul : Bool) (level : Nat) (strain : Strain) (over : Nat) : Int :=
  let points := contractPoints level strain
  let gameBonus : Int := if 100 ≤ points then (if vul then 500 else 300) else 50
  let slamBonus : Int :=
    if level = 6 then (if vul then 750 else 500)
    else if level = 7 then (if vul then 1500 else 1000)
    else 0
  points + over * perTrick strain + gameBonus + slamBonus
```

This is the undoubled score. `over` is the number of overtricks. The score adds up:
- **`points`:** the tricks bid.
- **`over * perTrick strain`:** overtricks at the trick value. There's no extra 10 for notrump, as that
  applies only to the first trick.
- **`gameBonus`:** 300 for game (500 vulnerable), or 50 for a part score.
- **`slamBonus`:** 500 for a small slam (750 vulnerable), 1,000 for a grand slam (1,500 vulnerable).

There's no doubling here, because in this model a contract that makes is never doubled.

**Examples:**

| Contract | Not vulnerable | Vulnerable |
|---|---|---|
| 1NT | 90 | |
| 2♦ | 90 | |
| 2♠ | 110 | |
| 3NT | 400 | 600 |
| 3NT + 1 | 430 | |
| 4♥ + 2 | 480 | |
| 4♠ | | 620 |
| 4♣ | 130 | |
| 5♣ | 400 | |
| 6NT | 990 | 1,440 |
| 7♠ | 1,510 | 2,210 |
| 7NT | | 2,220 |

**Check:** the amounts in all four parts.

### Penalty for going down (lines 51–54)

```lean
def doubledPenalty (vul : Bool) (down : Nat) : Int :=
  if vul then 300 * (down : Int) - 100
  else if down ≤ 3 then 200 * (down : Int) - 100
  else 300 * (down : Int) - 400
```

The doubled penalty, written as formulas rather than a table. Working them out:

| Down | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| Not vulnerable | 100 | 300 | 500 | 800 | 1,100 |
| Vulnerable | 200 | 500 | 800 | 1,100 | 1,400 |

Only doubled penalties exist in this file, because a contract that fails is always scored doubled.

**Check:** these match the doubled scoring table.

### The declaring side's score (lines 57–59)

```lean
def declarerScore (vul : Bool) (level : Nat) (strain : Strain) (tricks : Nat) : Int :=
  if level + 6 ≤ tricks then madeScore vul level strain (tricks - (level + 6))
  else - doubledPenalty vul (level + 6 - tricks)
```

`level + 6` is the tricks needed. With enough tricks, declarer scores `madeScore`, with the excess as
overtricks. Otherwise it's minus the penalty for the shortfall. Each subtraction happens only on the
side of the `if` where it can't go below 0.

**Examples:** not vulnerable, 3NT with 9 tricks is +400, with 10 is +430, and with 8 is -100.
Vulnerable, 3NT with 7 tricks is -500.

**Check:** this is where the model's main scoring choice sits: **make undoubled, fail doubled**.

### Contract numbers (lines 64–72)

```lean
def levelOf (no : Nat) : Nat := (no - 1) / 5 + 1
```

```lean
def strainOf (no : Nat) : Strain :=
  match (no - 1) % 5 with
  | 0 => some .clubs
  | 1 => some .diamonds
  | 2 => some .hearts
  | 3 => some .spades
  | _ => none
```

Each contract is a number from 1 to 35 in bidding order, so "a higher bid" is simply a higher number:

| Number | 1 | 2 | 3 | 4 | 5 | 6 | ... | 15 | ... | 35 |
|---|---|---|---|---|---|---|---|---|---|---|
| Contract | 1♣ | 1♦ | 1♥ | 1♠ | 1NT | 2♣ | ... | 3NT | ... | 7NT |

Number 0 means nobody has bid.

**Check:** clubs, diamonds, hearts, spades, notrump is the bidding order.

### The table (line 75)

```lean
abbrev Table := Strain → Seat → Nat
```

A double-dummy table: given a strain and a declarer, it gives the tricks declarer takes.

### Score if the auction ends here (lines 79–85)

```lean
def finalScore (t : Table) (v : Vulnerability) (no : Nat) (d : Seat) : Int :=
  if no = 0 then 0
  else
    let s := declarerScore (v.of d.side) (levelOf no) (strainOf no) (t (strainOf no) d)
    match d.side with
    | .ns => s
    | .ew => -s
```

The final score if contract `no` by declarer `d` is played:
- Contract 0 means the deal was passed out, for 0.
- Otherwise `s` is the declaring side's score, using their vulnerability and the tricks from the table.
- **Every score is from North-South's point of view**, so East-West's score has its sign flipped.

**Check:** the vulnerability is the declaring side's, and the sign flips only for East-West.

### Each player's choice (lines 88–91)

```lean
def best (side : Side) (pass : Int) (bids : List Int) : Int :=
  match side with
  | .ns => bids.foldl max pass
  | .ew => bids.foldl min pass
```

`pass` is the result if this player passes, and `bids` the result of each possible bid. North-South
take the highest and East-West the lowest, which is right because scores are from North-South's point
of view.

**Example:** choosing between a pass worth 5 and bids worth 3 or 7, North-South get 7 and East-West get 3.

**Check:** North-South maximize and East-West minimize. Card play has a strategy theorem protecting
against these being swapped, but the auction doesn't, so this one is worth a careful look.

### When the auction ends (line 94)

```lean
def passesToEnd (no : Nat) : Nat := if no = 0 then 4 else 3
```

Four passes in a row if nobody has bid, and otherwise three.

**Check:** these are the rules for ending an auction.

### The auction game (lines 99–106)

This is the most important definition in the file.

```lean
def auctionValue (t : Table) (v : Vulnerability) : (fuel : Nat) → (no : Nat) → (d seat : Seat) →
    (p : Nat) → Int
  | 0, _, _, _, _ => 0
  | fuel + 1, no, d, seat, p =>
    if p = passesToEnd no then finalScore t v no d
    else
      best seat.side (auctionValue t v fuel no d seat.next (p + 1))
        ((List.range' (no + 1) (35 - no)).map fun b => auctionValue t v fuel b seat seat.next 0)
```

This gives the result of the auction from any point, with best bidding by both sides. It describes the
position with:
- `no` and `d`: the contract so far, and its declarer.
- `seat`: whose turn it is.
- `p`: how many passes in a row there have been.
- `fuel`: a limit on how far it looks ahead, explained below.

Then:
- If there have been enough passes, the auction is over, and the score is `finalScore`.
- Otherwise `seat` chooses, using `best`, between:
  - **Passing:** play moves to the next seat, with the same contract and one more pass.
  - **Bidding:** `List.range' (no + 1) (35 - no)` lists every contract from `no + 1` up to 35. Bidding
    `b` makes it the new contract, with `seat` as its declarer, and resets the passes to 0.

Points to notice:
- **The bidder is the declarer.**
- **Anyone can bid over anyone,** including their own partner or their own earlier bid.
- **There's no double or redouble move.** Doubling happens automatically through `declarerScore`.

**Fuel:** the first line returns 0 if `fuel` runs out, which would be wrong if it could happen. Each step
uses one unit, and the proof behind `parScore_eq_parFast` shows that 180 is always enough, so the 200 in
`parScore` never runs out.

**Check:** this is the game you mean by par, and both the pass and the bid are handled correctly.

### Par (lines 109–110)

```lean
def parScore (t : Table) (v : Vulnerability) (dealer : Seat) : Int :=
  auctionValue t v 200 0 .north dealer 0
```

Par is the game's result at the start: contract 0, the dealer to act and no passes yet. The `.north`
is a placeholder for the declarer, which doesn't matter because contract 0 scores 0.

**Examples:**

- **North-South alone can make 3NT:** par is +400, or +600 vulnerable.
- **East-West alone can make 3NT:** par is -400.
- **A sacrifice:** North-South make 4♠ for +420, while East-West can take 9 tricks in clubs. Nobody is
  vulnerable, so 5♣ doubled goes down two for 300, better for East-West than conceding 420. 5♠ would
  fail, so par is +300. If East-West are vulnerable, the same sacrifice costs 500, so they don't bid
  it, and par is +420.
- **The dealer decides:** North and East can each make 1NT and nothing else. Whichever is reached first
  clockwise from the dealer bids it. With North dealing, par is +90. With East dealing it's -90. With
  South dealing it's +90, as North comes first after West, and with West dealing it's also +90.

**Check:** the dealer acts first, and positive scores favor North-South.

### Declarer's tricks (lines 114–117)

```lean
def declarerTricks (h : Hands) (strain : Strain) (d : Seat) : Nat :=
  match d.side with
  | .ns => nsTricks strain h d.next
  | .ew => 13 - nsTricks strain h d.next
```

This builds the table from the deal, using the proved double-dummy results from
[Rules.lean](Rules.lean). `d.next` is the seat to declarer's left, who leads. `nsTricks` counts North-South's
tricks, so East-West's declarer takes the rest of the 13.

**Check:** the opening leader sits to declarer's left, and the East-West case counts declarer's own side.

### Par for a deal (lines 120–121)

```lean
def dealPar (h : Hands) (v : Vulnerability) (dealer : Seat) : Int :=
  parScore (declarerTricks h) v dealer
```

This is what the generated par theorems are about: par for a deal, from its true double-dummy table.

**Check:** you can stop here. The rest of the file doesn't need review.

## 3. Checklist

- [ ] **Vulnerability:** `Vulnerability.of`
- [ ] **Trick values:** `perTrick`, `contractPoints`
- [ ] **Bonuses and overtricks:** `madeScore`
- [ ] **Penalties:** `doubledPenalty` matches the table above
- [ ] **Make or fail:** `declarerScore`
- [ ] **Bidding order:** `levelOf`, `strainOf`
- [ ] **Signs:** `finalScore` flips only for East-West
- [ ] **Choices:** `best`, North-South highest and East-West lowest
- [ ] **Ending the auction:** `passesToEnd`
- [ ] **The game:** `auctionValue` is what you mean by par
- [ ] **Start of the auction:** `parScore`
- [ ] **The table:** `declarerTricks`, with the leader to declarer's left
