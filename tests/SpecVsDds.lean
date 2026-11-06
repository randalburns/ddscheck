import DdsCheck.Rules

/-! Compare the Lean `value` function, evaluated directly, with DDS on small endgames. -/

open Bridge

def suitOf : Nat → Suit
  | 0 => .spades | 1 => .hearts | 2 => .diamonds | _ => .clubs

def seatOf : Nat → Seat
  | 0 => .north | 1 => .east | 2 => .south | _ => .west

def parseLine (nums : List Nat) : Option (Strain × Seat × Nat × Hands) := do
  let strain :: leader :: ns :: rest := nums | none
  let takeHand (l : List Nat) : Option (List Card × List Nat) := do
    let n :: l := l | none
    pure ((l.take n).map (fun b => ⟨suitOf (b / 16), b % 16⟩), l.drop n)
  let (north, r) ← takeHand rest
  let (east, r) ← takeHand r
  let (south, r) ← takeHand r
  let (west, _) ← takeHand r
  pure (if strain == 4 then none else some (suitOf strain), seatOf leader, ns,
    { north, east, south, west })

def main (args : List String) : IO UInt32 := do
  let lines ← IO.FS.lines (args.head!)
  let mut same := 0
  let mut different := 0
  for line in lines do
    let nums := (line.splitOn " ").filterMap String.toNat?
    let some (strain, leader, ns, h) := parseLine nums | throw (IO.userError s!"bad line: {line}")
    let got := value strain h.cards.length (start h leader)
    if got == ns then
      same := same + 1
    else
      different := different + 1
      IO.println s!"DIFFERENT: Lean {got}, DDS {ns}: {line}"
  IO.println s!"{same} agree, {different} differ"
  return if different == 0 then 0 else 1
