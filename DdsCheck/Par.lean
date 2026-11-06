import DdsCheck.Rules

/-!
# Scoring and par

This file is part of the trusted specification, down to `dealPar`: it states duplicate scoring
and the game that defines par. Par is the result of an auction in which all four players see
all the cards and know every double-dummy result.

Following DDS's definition: a contract that fails is scored doubled, and one that makes is
scored undoubled, since with open cards the defenders double exactly when it fails.
Whoever makes the winning bid declares.
There are no double or redouble moves.

`auctionValue` is too slow to evaluate, so `parFast` is a table-based version, and
`parScore_eq_parFast` proves by induction that they always agree.
-/

namespace Bridge

inductive Vulnerability | none | both | ns | ew
  deriving DecidableEq, Repr, Inhabited

def Vulnerability.of (v : Vulnerability) : Side → Bool
  | .ns => v == .both || v == .ns
  | .ew => v == .both || v == .ew

/-! ## Scoring -/

/-- Points for each trick: 20 in the minors, 30 in the majors and notrump. -/
def perTrick : Strain → Int
  | some .clubs | some .diamonds => 20
  | _ => 30

/-- Points for the tricks bid; notrump earns an extra 10 for the first. -/
def contractPoints (level : Nat) (strain : Strain) : Int :=
  level * perTrick strain + if strain = none then 10 else 0

/-- Score for making a contract undoubled, with `over` overtricks. -/
def madeScore (vul : Bool) (level : Nat) (strain : Strain) (over : Nat) : Int :=
  let points := contractPoints level strain
  let gameBonus : Int := if 100 ≤ points then (if vul then 500 else 300) else 50
  let slamBonus : Int :=
    if level = 6 then (if vul then 750 else 500)
    else if level = 7 then (if vul then 1500 else 1000)
    else 0
  points + over * perTrick strain + gameBonus + slamBonus

/-- Penalty for going down `down` tricks doubled. Vulnerable: 200, then 300 each. Not
vulnerable: 100, then 200 each for the second and third, then 300 each. -/
def doubledPenalty (vul : Bool) (down : Nat) : Int :=
  if vul then 300 * (down : Int) - 100
  else if down ≤ 3 then 200 * (down : Int) - 100
  else 300 * (down : Int) - 400

/-- The declaring side's score, for a contract and the tricks declarer takes. -/
def declarerScore (vul : Bool) (level : Nat) (strain : Strain) (tricks : Nat) : Int :=
  if level + 6 ≤ tricks then madeScore vul level strain (tricks - (level + 6))
  else - doubledPenalty vul (level + 6 - tricks)

/-! ## Contracts and the auction -/

/-- A contract number from 1 to 35, in bidding order: 1C = 1, 1D, 1H, 1S, 1NT, 2C, ..., 7NT = 35. -/
def levelOf (no : Nat) : Nat := (no - 1) / 5 + 1

def strainOf (no : Nat) : Strain :=
  match (no - 1) % 5 with
  | 0 => some .clubs
  | 1 => some .diamonds
  | 2 => some .hearts
  | 3 => some .spades
  | _ => none

/-- A double-dummy table: the tricks declarer takes, for each strain and declarer. -/
abbrev Table := Strain → Seat → Nat

/-- The score from North-South's point of view, if the auction ends in contract `no` by `d`.
Contract 0 means nobody bid, so the deal is passed out. -/
def finalScore (t : Table) (v : Vulnerability) (no : Nat) (d : Seat) : Int :=
  if no = 0 then 0
  else
    let s := declarerScore (v.of d.side) (levelOf no) (strainOf no) (t (strainOf no) d)
    match d.side with
    | .ns => s
    | .ew => -s

/-- The result of a player's choice: North-South want the highest score, East-West the lowest. -/
def best (side : Side) (pass : Int) (bids : List Int) : Int :=
  match side with
  | .ns => bids.foldl max pass
  | .ew => bids.foldl min pass

/-- An auction ends after four passes if nobody has bid, and otherwise after three in a row. -/
def passesToEnd (no : Nat) : Nat := if no = 0 then 4 else 3

/-- **The auction game.** The current contract is `no` by `d`, `seat` is to act, and there have
been `p` passes in a row. The player either passes, or bids any higher contract and becomes
its declarer. `fuel` only bounds the recursion; an auction is far shorter than `parScore`'s 200. -/
def auctionValue (t : Table) (v : Vulnerability) : (fuel : Nat) → (no : Nat) → (d seat : Seat) →
    (p : Nat) → Int
  | 0, _, _, _, _ => 0
  | fuel + 1, no, d, seat, p =>
    if p = passesToEnd no then finalScore t v no d
    else
      best seat.side (auctionValue t v fuel no d seat.next (p + 1))
        ((List.range' (no + 1) (35 - no)).map fun b => auctionValue t v fuel b seat seat.next 0)

/-- **Par:** the auction's result with `dealer` first to act. Positive favors North-South. -/
def parScore (t : Table) (v : Vulnerability) (dealer : Seat) : Int :=
  auctionValue t v 200 0 .north dealer 0

/-- Declarer's tricks: North-South's total, or the rest of the 13 for East-West. The opening
leader sits to declarer's left. -/
def declarerTricks (h : Hands) (strain : Strain) (d : Seat) : Nat :=
  match d.side with
  | .ns => nsTricks strain h d.next
  | .ew => 13 - nsTricks strain h d.next

/-- **Par for a deal**, from its true double-dummy results. -/
def dealPar (h : Hands) (v : Vulnerability) (dealer : Seat) : Int :=
  parScore (declarerTricks h) v dealer

/-! ## A fast evaluator, proved equal to the game -/

structure Row where
  north : Int
  east : Int
  south : Int
  west : Int
  deriving Inhabited

def Row.get (r : Row) : Seat → Int
  | .north => r.north | .east => r.east | .south => r.south | .west => r.west

def Row.ofFn (g : Seat → Int) : Row := ⟨g .north, g .east, g .south, g .west⟩

theorem Row.get_ofFn (g : Seat → Int) (s : Seat) : (Row.ofFn g).get s = g s := by
  cases s <;> rfl

/-- A player's choice, given the results of bidding each higher contract. -/
def choice (rows : List Row) (seat : Seat) (pass : Int) : Int :=
  best seat.side pass (rows.map (·.get seat))

/-- For each declarer: the result once contract `no` has just been bid, with the other three
players still to act and `rows` holding the results for each higher contract. -/
def mkRow (t : Table) (v : Vulnerability) (no : Nat) (rows : List Row) : Row :=
  Row.ofFn fun d =>
    choice rows d.next (choice rows d.next.next (choice rows d.next.next.next (finalScore t v no d)))

/-- The rows for contracts `36 - k` to 35, lowest first. -/
def rowsAbove (t : Table) (v : Vulnerability) : Nat → List Row
  | 0 => []
  | k + 1 =>
    let rows := rowsAbove t v k
    mkRow t v (35 - k) rows :: rows

/-- Par, computed from the rows for contracts 1 to 35. -/
def parFast (t : Table) (v : Vulnerability) (dealer : Seat) : Int :=
  let rows := rowsAbove t v 35
  choice rows dealer (choice rows dealer.next (choice rows dealer.next.next
    (choice rows dealer.next.next.next 0)))

theorem auction_continue {t : Table} {v : Vulnerability} {f no : Nat} {d seat : Seat} {p : Nat}
    (h : p ≠ passesToEnd no) :
    auctionValue t v (f + 1) no d seat p =
      best seat.side (auctionValue t v f no d seat.next (p + 1))
        ((List.range' (no + 1) (35 - no)).map fun b => auctionValue t v f b seat seat.next 0) := by
  simp [auctionValue, h]

theorem auction_over {t : Table} {v : Vulnerability} {f no : Nat} {d seat : Seat} {p : Nat}
    (h : p = passesToEnd no) :
    auctionValue t v (f + 1) no d seat p = finalScore t v no d := by
  simp [auctionValue, h]

/-- **The induction, on the number of contracts above.** Each row holds the game's value for the
contract just bid, with any fuel that is sufficient. -/
theorem rows_spec (t : Table) (v : Vulnerability) (k : Nat) (hk : k ≤ 35) (seat : Seat) (f : Nat)
    (hf : k * 5 ≤ f) :
    (rowsAbove t v k).map (·.get seat)
      = (List.range' (36 - k) k).map fun b => auctionValue t v f b seat seat.next 0 := by
  induction k generalizing seat f with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ 35 := by omega
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
    have hg : k * 5 ≤ g := by omega
    have hrange : List.range' (36 - (k + 1)) (k + 1) = (35 - k) :: List.range' (36 - k) k := by
      have h1 : 36 - (k + 1) = 35 - k := by omega
      have h2 : 35 - k + 1 = 36 - k := by omega
      rw [h1, List.range'_succ, h2]
    have hno : passesToEnd (35 - k) = 3 := by
      have : 35 - k ≠ 0 := by omega
      simp [passesToEnd, this]
    have hbids : ∀ (s : Seat) (j : Nat), k * 5 ≤ j →
        ((List.range' (35 - k + 1) (35 - (35 - k))).map fun b => auctionValue t v j b s s.next 0)
          = (rowsAbove t v k).map (·.get s) := by
      intro s j hj
      have h1 : 35 - k + 1 = 36 - k := by omega
      have h2 : 35 - (35 - k) = k := by omega
      rw [h1, h2]
      exact (ih hk' s j hj).symm
    have hhead : (mkRow t v (35 - k) (rowsAbove t v k)).get seat
        = auctionValue t v (g + 4) (35 - k) seat seat.next 0 := by
      rw [auction_continue (by omega), hbids _ _ (by omega)]
      rw [auction_continue (by omega), hbids _ _ (by omega)]
      rw [auction_continue (by omega), hbids _ _ (by omega)]
      rw [auction_over (by omega)]
      simp [mkRow, Row.get_ofFn, choice]
    rw [hrange]
    simp only [rowsAbove, List.map_cons]
    rw [hhead, ih hk' seat (g + 4) (by omega)]

/-- **The game's value is what the fast evaluator computes.** -/
theorem parScore_eq_parFast (t : Table) (v : Vulnerability) (dealer : Seat) :
    parScore t v dealer = parFast t v dealer := by
  have hrows : ∀ (s : Seat) (j : Nat), 175 ≤ j →
      ((List.range' (0 + 1) (35 - 0)).map fun b => auctionValue t v j b s s.next 0)
        = (rowsAbove t v 35).map (·.get s) := by
    intro s j hj
    exact (rows_spec t v 35 (by omega) s j (by omega)).symm
  have hend : passesToEnd 0 = 4 := by simp [passesToEnd]
  have hfinal : finalScore t v 0 .north = 0 := by simp [finalScore]
  unfold parScore
  rw [show (200 : Nat) = 195 + 5 from rfl]
  rw [auction_continue (by omega), hrows _ _ (by omega)]
  rw [auction_continue (by omega), hrows _ _ (by omega)]
  rw [auction_continue (by omega), hrows _ _ (by omega)]
  rw [auction_continue (by omega), hrows _ _ (by omega)]
  rw [auction_over (by omega), hfinal]
  rfl

/-- Filling in a known table: this is how a deal's proved results become its par. -/
theorem dealPar_eq (h : Hands) (v : Vulnerability) (dealer : Seat) (t : Table)
    (ht : declarerTricks h = t) : dealPar h v dealer = parFast t v dealer := by
  rw [dealPar, ht, parScore_eq_parFast]

/-- Declarer's tricks, from a proved count for North-South. -/
theorem declarerTricks_of {h : Hands} {strain : Strain} {d : Seat} {k : Nat}
    (hk : nsTricks strain h d.next = k) :
    declarerTricks h strain d = match d.side with
      | .ns => k
      | .ew => 13 - k := by
  simp [declarerTricks, hk]

end Bridge
