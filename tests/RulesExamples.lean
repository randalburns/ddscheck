import DdsCheck.Checker

/-!
Small hand-checkable positions, proved by the Lean kernel alone with no compiled code,
no certificates and no DDS. Each tests one rule in `Rules.lean`. Ranks: 14 = ace, 13 = king, ...
-/

namespace Bridge.Examples

def sp (r : Nat) : Card := ⟨.spades, r⟩
def he (r : Nat) : Card := ⟨.hearts, r⟩
def cl (r : Nat) : Card := ⟨.clubs, r⟩

/-- The higher card of the suit led wins. -/
example : value none 4 (start ⟨[sp 14], [sp 2], [sp 3], [sp 4]⟩ .north) = 1 := by decide +kernel

/-- East's king beats North's queen, even though North led. -/
example : value none 4 (start ⟨[sp 12], [sp 13], [sp 3], [sp 4]⟩ .north) = 0 := by decide +kernel

/-- In notrump a discard never wins: East's ace of hearts does not beat the lead. -/
example : value none 4 (start ⟨[sp 2], [he 14], [cl 3], [cl 4]⟩ .north) = 1 := by decide +kernel

/-- With spades as trumps, the smallest trump beats the ace of another suit. -/
example : value (some .spades) 4 (start ⟨[he 14], [sp 2], [he 3], [he 4]⟩ .north) = 0 := by
  decide +kernel

/-- Of two trumps, the higher wins. -/
example : value (some .spades) 4 (start ⟨[he 14], [sp 2], [sp 3], [he 4]⟩ .north) = 1 := by
  decide +kernel

/-- A player holding the suit led must follow: East cannot ruff with the trump while
holding a heart, so North's ace wins this trick and the king of trumps wins the next. -/
example : value (some .spades) 8
    (start ⟨[he 14, sp 13], [he 2, sp 3], [he 3, cl 2], [he 4, cl 3]⟩ .north) = 2 := by decide +kernel

/-- The winner of a trick leads to the next one. North-South hold the two top cards in the
suit that East-West cannot avoid being on lead in; East wins the first trick and must then
lead a heart into North's ace, so North-South take exactly one. -/
example : value none 8
    (start ⟨[he 14, cl 2], [he 2, sp 14], [he 3, cl 3], [he 4, cl 4]⟩ .east) = 1 := by decide +kernel

/-- **A finesse.** South leads towards North's ace-queen with West holding the king: North-South
take both tricks. Move the king to East, and the finesse loses. -/
example : value none 8
    (start ⟨[sp 14, sp 12], [cl 14, cl 13], [sp 2, sp 3], [sp 13, sp 4]⟩ .south) = 2 := by
  decide +kernel

example : value none 8
    (start ⟨[sp 14, sp 12], [sp 13, sp 4], [sp 2, sp 3], [cl 14, cl 13]⟩ .south) = 1 := by
  decide +kernel

end Bridge.Examples

#print axioms Bridge.value_canon
#print axioms Bridge.checkClaim_sound
