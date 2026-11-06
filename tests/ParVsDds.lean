import DdsCheck.Par

/-! Compare the Lean par evaluator with DDS's DealerPar. Takes the output of `par_vs_dds`. -/

open Bridge

def strainAt : Nat → Strain
  | 0 => some .spades | 1 => some .hearts | 2 => some .diamonds | 3 => some .clubs | _ => none

def strainIndex : Strain → Nat
  | some .spades => 0 | some .hearts => 1 | some .diamonds => 2 | some .clubs => 3 | none => 4

def seatIndex : Seat → Nat
  | .north => 0 | .east => 1 | .south => 2 | .west => 3

def seatAt : Nat → Seat
  | 0 => .north | 1 => .east | 2 => .south | _ => .west

def vulAt : Nat → Vulnerability
  | 0 => .none | 1 => .both | 2 => .ns | _ => .ew

def main (args : List String) : IO UInt32 := do
  let mut lines := 0
  let mut differ := 0
  let mut sensitive := 0
  for path in args do
    for line in ← IO.FS.lines path do
      let parts := (line.splitOn " ").filter (· != "")
      let nums := (parts.take 22).filterMap String.toNat?
      let some score := (parts.getD 22 "").toInt? | throw (IO.userError s!"bad line: {line}")
      if nums.length != 22 then throw (IO.userError s!"bad line: {line}")
      let entries := nums.toArray
      let t : Table := fun strain d => entries[strainIndex strain * 4 + seatIndex d]!
      let v := vulAt (entries[20]!)
      let got := parFast t v (seatAt (entries[21]!))
      lines := lines + 1
      if got != score then
        differ := differ + 1
        if differ ≤ 10 then IO.println s!"DIFFERENT: Lean {got}, DDS {score}: {line}"
      let all := [Seat.north, .east, .south, .west].map (parFast t v)
      if all.any (· != all.head!) then sensitive := sensitive + 1
  IO.println s!"{lines} cases: {lines - differ} agree, {differ} differ; {sensitive} are dealer-sensitive"
  return if differ == 0 && lines > 0 then 0 else 1
