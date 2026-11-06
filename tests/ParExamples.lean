import DdsCheck.Par

/-!
Scoring and auction results you can check by hand, proved by the Lean kernel alone.
-/

namespace Bridge.ParExamples

/-! ## Contracts made, undoubled -/

example : madeScore false 1 none 0 = 90 := by decide            -- 1NT
example : madeScore false 2 (some .diamonds) 0 = 90 := by decide -- 2D
example : madeScore false 2 (some .spades) 0 = 110 := by decide  -- 2S
example : madeScore false 3 none 0 = 400 := by decide            -- 3NT
example : madeScore true 3 none 0 = 600 := by decide
example : madeScore false 3 none 1 = 430 := by decide            -- 3NT with an overtrick
example : madeScore false 4 (some .hearts) 0 = 420 := by decide  -- 4H
example : madeScore true 4 (some .spades) 0 = 620 := by decide
example : madeScore false 4 (some .hearts) 2 = 480 := by decide  -- 4H with two overtricks
example : madeScore false 4 (some .clubs) 0 = 130 := by decide   -- 4C is not game
example : madeScore false 5 (some .clubs) 0 = 400 := by decide   -- 5C is game
example : madeScore true 5 (some .diamonds) 0 = 600 := by decide
example : madeScore false 6 none 0 = 990 := by decide            -- 6NT
example : madeScore true 6 none 0 = 1440 := by decide
example : madeScore false 6 (some .clubs) 0 = 920 := by decide
example : madeScore false 7 (some .spades) 0 = 1510 := by decide -- 7S
example : madeScore true 7 (some .spades) 0 = 2210 := by decide
example : madeScore true 7 none 0 = 2220 := by decide            -- 7NT

/-! ## Contracts defeated, doubled -/

example : doubledPenalty false 1 = 100 := by decide
example : doubledPenalty false 2 = 300 := by decide
example : doubledPenalty false 3 = 500 := by decide
example : doubledPenalty false 4 = 800 := by decide
example : doubledPenalty false 5 = 1100 := by decide
example : doubledPenalty true 1 = 200 := by decide
example : doubledPenalty true 2 = 500 := by decide
example : doubledPenalty true 3 = 800 := by decide

example : declarerScore false 3 none 9 = 400 := by decide
example : declarerScore false 3 none 10 = 430 := by decide
example : declarerScore false 3 none 8 = -100 := by decide
example : declarerScore true 3 none 7 = -500 := by decide

/-! ## Contract numbers -/

example : levelOf 1 = 1 ∧ strainOf 1 = some .clubs := by decide
example : levelOf 5 = 1 ∧ strainOf 5 = none := by decide
example : levelOf 6 = 2 ∧ strainOf 6 = some .clubs := by decide
example : levelOf 15 = 3 ∧ strainOf 15 = none := by decide
example : levelOf 35 = 7 ∧ strainOf 35 = none := by decide

/-! ## Auctions -/

/-- Nobody can make anything, so the deal is passed out. -/
def nothing : Table := fun _ _ => 6
example : parFast nothing .none .north = 0 := by decide +kernel

/-- North-South alone can make 3NT, and bid it. -/
def gameNS : Table := fun strain d =>
  match strain, d.side with
  | none, .ns => 9
  | _, _ => 3
example : parFast gameNS .none .north = 400 := by decide +kernel
example : parFast gameNS .both .north = 600 := by decide +kernel
example : parFast gameNS .ew .east = 400 := by decide +kernel

/-- East-West make the same contract, so the sign flips. -/
def gameEW : Table := fun strain d =>
  match strain, d.side with
  | none, .ew => 9
  | _, _ => 3
example : parFast gameEW .none .north = -400 := by decide +kernel

/-- **A sacrifice.** North-South make 4S for +420, but East-West can take nine tricks in clubs:
5C doubled goes down two for only -300, and 5S would fail. So par is North-South +300. -/
def sacrifice : Table := fun strain d =>
  match strain, d.side with
  | some .spades, .ns => 10
  | some .clubs, .ew => 9
  | _, _ => 3
example : parFast sacrifice .none .north = 300 := by decide +kernel

/-- If East-West are vulnerable, the same sacrifice costs -500: worse than conceding 4S. -/
example : parFast sacrifice .ew .north = 420 := by decide +kernel

/-- **The dealer decides.** North and East can each make 1NT and nothing else. Whichever of them
is reached first in clockwise order from the dealer bids it. -/
def firstToBid : Table := fun strain d =>
  match strain, d with
  | none, .north | none, .east => 7
  | _, _ => 3
example : parFast firstToBid .none .north = 90 := by decide +kernel
example : parFast firstToBid .none .east = -90 := by decide +kernel
example : parFast firstToBid .none .south = 90 := by decide +kernel
example : parFast firstToBid .none .west = 90 := by decide +kernel

/-- The same results through the game definition itself. -/
example : parScore firstToBid .none .east = -90 := by
  rw [parScore_eq_parFast]; decide +kernel

end Bridge.ParExamples

#print axioms Bridge.parScore_eq_parFast
