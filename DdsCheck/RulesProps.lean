import DdsCheck.Rules

/-!
# What the rules do, for every position

Part 1 is the induction: the value of a game of any size is determined by what `legal` and
`step` do on the positions reachable in it. So nothing about the rules can go wrong only at
larger sizes.

Part 2 states what `legal` and `step` do. Each theorem covers all positions. To review the
rules of bridge, you can read these statements instead of the code in `Rules.lean`.

These prove the definitions have these properties. That the properties are the rules of
bridge is for a person to judge, since bridge itself has no definition in Lean.
-/

namespace Bridge

/-! ## Part 1: the value is determined by one step of play -/

/-- Any other candidate for the rules: which cards may be played, and what playing one does. -/
structure AltRules where
  legal : State → List Card
  step : State → Card → State × Option Seat

/-- The same maximizing and minimizing as `value`, over candidate rules. -/
def minimax (R : AltRules) : Nat → State → Nat
  | 0, _ => 0
  | n + 1, s =>
    let outcomes := (R.legal s).map fun c =>
      let r := R.step s c
      nsPoint r.2 + minimax R n r.1
    match s.turn.side with
    | .ns => maxOf outcomes
    | .ew => minOf outcomes

/-- `t` can arise from `s` by legal play. -/
inductive Reachable (strain : Strain) (s : State) : State → Prop
  | refl : Reachable strain s s
  | play {t : State} {c : Card} : Reachable strain s t → c ∈ legal t →
      Reachable strain s (step strain t c).1

/-- **The induction.** Rules that agree with `legal` and `step` on the positions reachable
from `s` give the same value from `s`, however many cards are left to play. -/
theorem minimax_eq_value (strain : Strain) (R : AltRules) (s : State)
    (hlegal : ∀ t, Reachable strain s t → R.legal t = legal t)
    (hstep : ∀ t c, Reachable strain s t → c ∈ legal t → R.step t c = step strain t c)
    (n : Nat) : minimax R n s = value strain n s := by
  suffices h : ∀ t, Reachable strain s t → minimax R n t = value strain n t from h s .refl
  induction n with
  | zero => intro t _; rfl
  | succ n ih =>
    intro t ht
    have houts : ((R.legal t).map fun c => nsPoint (R.step t c).2 + minimax R n (R.step t c).1)
        = (legal t).map fun c => nsPoint (step strain t c).2 + value strain n (step strain t c).1 := by
      rw [hlegal t ht]
      apply List.map_congr_left
      intro c hc
      rw [hstep t c ht hc, ih _ (.play ht hc)]
    simp only [minimax, value, houts]
    cases t.turn.side <;> rfl

/-- A sanity check that the hypotheses can be met: `legal` and `step` agree with themselves. -/
example (strain : Strain) (n : Nat) (s : State) :
    minimax ⟨legal, step strain⟩ n s = value strain n s :=
  minimax_eq_value strain _ s (fun _ _ => rfl) (fun _ _ _ _ => rfl) n

/-! ## Part 2: legal plays -/

/-- You can only play a card from the hand of the player whose turn it is. -/
theorem legal_mem_hand (s : State) {c : Card} (h : c ∈ legal s) : c ∈ s.hands.get s.turn := by
  unfold legal at h
  split at h
  · exact h
  · simp only at h
    split at h
    · exact h
    · exact (List.mem_filter.mp h).1

/-- On a lead, any card in the hand may be played. -/
theorem legal_lead {s : State} (h : s.trick = []) : legal s = s.hands.get s.turn := by
  simp [legal, h]

/-- If you hold the suit led, you may play exactly your cards of that suit. -/
theorem legal_follow {s : State} {first : Seat × Card} {rest : List (Seat × Card)}
    (h : s.trick = first :: rest)
    (holds : ∃ x ∈ s.hands.get s.turn, x.suit = first.2.suit) (c : Card) :
    c ∈ legal s ↔ c ∈ s.hands.get s.turn ∧ c.suit = first.2.suit := by
  obtain ⟨x, hx, hxs⟩ := holds
  have hne : ((s.hands.get s.turn).filter (·.suit == first.2.suit)).isEmpty = false := by
    cases hf : (s.hands.get s.turn).filter (·.suit == first.2.suit) with
    | nil =>
      have : x ∈ (s.hands.get s.turn).filter (·.suit == first.2.suit) :=
        List.mem_filter.mpr ⟨hx, by simp [hxs]⟩
      simp [hf] at this
    | cons _ _ => rfl
  rcases first with ⟨seat, led⟩
  simp only [] at hne
  simp [legal, h, hne, List.mem_filter]

/-- If you are void in the suit led, any card in the hand may be played. -/
theorem legal_void {s : State} {first : Seat × Card} {rest : List (Seat × Card)}
    (h : s.trick = first :: rest)
    (void : ∀ x ∈ s.hands.get s.turn, x.suit ≠ first.2.suit) :
    legal s = s.hands.get s.turn := by
  have hempty : (s.hands.get s.turn).filter (·.suit == first.2.suit) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simpa using void x hx
  rcases first with ⟨seat, led⟩
  simp only [] at hempty
  simp [legal, h, hempty]

/-! ## Part 2: playing a card -/

theorem step_hands (strain : Strain) (s : State) (c : Card) :
    (step strain s c).1.hands = s.hands.remove s.turn c := by
  unfold step
  simp only
  split <;> rfl

theorem get_remove_same (h : Hands) (seat : Seat) (c x : Card) :
    x ∈ (h.remove seat c).get seat ↔ x ∈ h.get seat ∧ x ≠ c := by
  cases seat <;> simp [Hands.remove, Hands.get, List.mem_filter]

theorem get_remove_other (h : Hands) {seat other : Seat} (c : Card) (hne : other ≠ seat) :
    (h.remove seat c).get other = h.get other := by
  cases seat <;> cases other <;> first | rfl | exact absurd rfl hne

/-- Playing a card takes it out of your hand and leaves the rest of your hand. -/
theorem play_removes_card (strain : Strain) (s : State) (c x : Card) :
    x ∈ (step strain s c).1.hands.get s.turn ↔ x ∈ s.hands.get s.turn ∧ x ≠ c := by
  rw [step_hands, get_remove_same]

/-- Playing a card leaves the other three hands alone. -/
theorem play_keeps_other_hands (strain : Strain) (s : State) (c : Card) {other : Seat}
    (hne : other ≠ s.turn) : (step strain s c).1.hands.get other = s.hands.get other := by
  rw [step_hands, get_remove_other _ _ hne]

/-- Until the fourth card, the card joins the trick, play passes clockwise, and no trick is won. -/
theorem step_continue (strain : Strain) (s : State) (c : Card) (h : s.trick.length < 3) :
    (step strain s c).1.trick = s.trick ++ [(s.turn, c)] ∧
      (step strain s c).1.turn = s.turn.next ∧ (step strain s c).2 = none := by
  match ht : s.trick, h with
  | [], _ => simp [step, ht]
  | [_], _ => simp [step, ht]
  | [_, _], _ => simp [step, ht]

/-- The fourth card completes the trick. The table is cleared, and the seat holding the
winning play is credited with the trick and leads next. -/
theorem step_complete (strain : Strain) (s : State) (c : Card) {p₁ p₂ p₃ : Seat × Card}
    (h : s.trick = [p₁, p₂, p₃]) :
    let w := (trickWinner strain p₁ [p₂, p₃, (s.turn, c)]).1
    (step strain s c).1.trick = [] ∧ (step strain s c).1.turn = w ∧ (step strain s c).2 = some w := by
  simp [step, h]

/-- North-South score a point exactly when one of them wins the trick. -/
theorem nsPoint_some (w : Seat) : nsPoint (some w) = if w.side = .ns then 1 else 0 := rfl

/-- No point is scored while a trick is unfinished. -/
theorem nsPoint_none : nsPoint none = 0 := rfl

/-- North and South are partners, as are East and West. -/
theorem partners : Seat.north.side = Seat.south.side ∧ Seat.east.side = Seat.west.side ∧
    Seat.north.side ≠ Seat.east.side := by decide

/-- Clockwise order visits every seat and returns after four plays. -/
theorem clockwise : Seat.north.next = .east ∧ Seat.east.next = .south ∧
    Seat.south.next = .west ∧ Seat.west.next = .north := by decide

/-! ## Part 2: who wins a trick -/

/-- What we keep true as the plays of a trick are examined in order. -/
structure WinnerInv (strain : Strain) (led : Suit) (best : Seat × Card)
    (seen : List (Seat × Card)) : Prop where
  mem : best ∈ seen
  /-- Once a trump has appeared, the best play is the highest trump. -/
  trump : (∃ p ∈ seen, strain = some p.2.suit) →
    strain = some best.2.suit ∧
      ∀ p ∈ seen, strain = some p.2.suit → p.2.rank ≤ best.2.rank
  /-- With no trump so far, the best play is the highest card of the suit led. -/
  noTrump : (∀ p ∈ seen, strain ≠ some p.2.suit) →
    best.2.suit = led ∧ ∀ p ∈ seen, p.2.suit = led → p.2.rank ≤ best.2.rank

theorem WinnerInv.start (strain : Strain) (first : Seat × Card) :
    WinnerInv strain first.2.suit first [first] where
  mem := by simp
  trump := by
    rintro ⟨p, hp, ht⟩
    simp only [List.mem_singleton] at hp
    subst hp
    refine ⟨ht, ?_⟩
    intro q hq _
    simp only [List.mem_singleton] at hq
    subst hq
    exact Nat.le_refl _
  noTrump := by
    intro _
    refine ⟨rfl, ?_⟩
    intro q hq _
    simp only [List.mem_singleton] at hq
    subst hq
    exact Nat.le_refl _

theorem WinnerInv.extend {strain : Strain} {led : Suit} {best : Seat × Card}
    {seen : List (Seat × Card)} (h : WinnerInv strain led best seen) (p : Seat × Card) :
    WinnerInv strain led (if beats strain p.2 best.2 then p else best) (seen ++ [p]) := by
  have hmem : ∀ {q}, q ∈ seen ++ [p] ↔ q ∈ seen ∨ q = p := by simp
  by_cases hb : beats strain p.2 best.2 = true
  · simp only [hb, ite_true]
    constructor
    · simp
    · intro _
      unfold beats at hb
      by_cases hs : p.2.suit = best.2.suit
      · simp only [hs, beq_self_eq_true, ite_true, decide_eq_true_eq] at hb
        by_cases hbt : strain = some best.2.suit
        · refine ⟨by rw [hs]; exact hbt, ?_⟩
          intro q hq hqt
          rcases hmem.mp hq with hq | rfl
          · have := (h.trump ⟨best, h.mem, hbt⟩).2 q hq hqt
            omega
          · exact Nat.le_refl _
        · rename_i hex
          obtain ⟨r, hr, hrt⟩ := hex
          rcases hmem.mp hr with hr | rfl
          · have := (h.trump ⟨r, hr, hrt⟩).1
            exact absurd this hbt
          · rw [hs] at hrt; exact absurd hrt hbt
      · have hb2 : (p.2.suit == best.2.suit) = false := by simpa using hs
        simp only [hb2, Bool.false_eq_true, ite_false, beq_iff_eq] at hb
        refine ⟨hb, ?_⟩
        intro q hq hqt
        rcases hmem.mp hq with hq | rfl
        · by_cases hbt : strain = some best.2.suit
          · have h1 := h.trump ⟨best, h.mem, hbt⟩
            rw [hbt] at hb
            exact absurd (Option.some.inj hb).symm hs
          · exact absurd (h.trump ⟨q, hq, hqt⟩).1 hbt
        · exact Nat.le_refl _
    · intro hnone
      have hp : strain ≠ some p.2.suit := hnone p (by simp)
      have hseen : ∀ q ∈ seen, strain ≠ some q.2.suit := fun q hq => hnone q (by simp [hq])
      obtain ⟨h1, h2⟩ := h.noTrump hseen
      unfold beats at hb
      by_cases hs : p.2.suit = best.2.suit
      · simp only [hs, beq_self_eq_true, ite_true, decide_eq_true_eq] at hb
        refine ⟨hs.trans h1, ?_⟩
        intro q hq hql
        rcases hmem.mp hq with hq | rfl
        · have := h2 q hq hql
          omega
        · exact Nat.le_refl _
      · have hb2 : (p.2.suit == best.2.suit) = false := by simpa using hs
        simp only [hb2, Bool.false_eq_true, ite_false, beq_iff_eq] at hb
        exact absurd hb hp
  · have hif : (if beats strain p.2 best.2 = true then p else best) = best := by simp [hb]
    rw [hif]
    have hb' : ¬ beats strain p.2 best.2 = true := hb
    unfold beats at hb'
    constructor
    · simp [h.mem]
    · rintro ⟨r, hr, hrt⟩
      have hbt : strain = some best.2.suit := by
        rcases hmem.mp hr with hr | rfl
        · exact (h.trump ⟨r, hr, hrt⟩).1
        · by_cases hs : r.2.suit = best.2.suit
          · rw [← hs]; exact hrt
          · have hb2 : (r.2.suit == best.2.suit) = false := by simpa using hs
            simp [hb2, hrt] at hb'
      refine ⟨hbt, ?_⟩
      intro q hq hqt
      rcases hmem.mp hq with hq | rfl
      · exact (h.trump ⟨best, h.mem, hbt⟩).2 q hq hqt
      · have hs : q.2.suit = best.2.suit := by
          rw [hbt] at hqt
          exact (Option.some.inj hqt).symm
        simp only [hs, beq_self_eq_true, ite_true, decide_eq_true_eq] at hb'
        omega
    · intro hnone
      have hseen : ∀ q ∈ seen, strain ≠ some q.2.suit := fun q hq => hnone q (by simp [hq])
      obtain ⟨h1, h2⟩ := h.noTrump hseen
      refine ⟨h1, ?_⟩
      intro q hq hql
      rcases hmem.mp hq with hq | rfl
      · exact h2 q hq hql
      · have hs : q.2.suit = best.2.suit := hql.trans h1.symm
        simp only [hs, beq_self_eq_true, ite_true, decide_eq_true_eq] at hb'
        omega

theorem winnerInv_foldl (strain : Strain) (led : Suit) (rest : List (Seat × Card))
    (best : Seat × Card) (seen : List (Seat × Card)) (h : WinnerInv strain led best seen) :
    WinnerInv strain led
      (rest.foldl (fun b p => if beats strain p.2 b.2 then p else b) best) (seen ++ rest) := by
  induction rest generalizing best seen with
  | nil => simpa using h
  | cons p ps ih =>
    have := ih _ _ (h.extend p)
    simpa using this

theorem winnerInv (strain : Strain) (first : Seat × Card) (rest : List (Seat × Card)) :
    WinnerInv strain first.2.suit (trickWinner strain first rest) (first :: rest) := by
  have := winnerInv_foldl strain first.2.suit rest first [first] (WinnerInv.start strain first)
  simpa [trickWinner] using this

/-- The winning play is one of the plays in the trick. -/
theorem winner_mem (strain : Strain) (first : Seat × Card) (rest : List (Seat × Card)) :
    trickWinner strain first rest ∈ first :: rest :=
  (winnerInv strain first rest).mem

/-- If any trump was played, the trick is won by the highest trump. -/
theorem winner_highest_trump {strain : Strain} {first : Seat × Card} {rest : List (Seat × Card)}
    (h : ∃ p ∈ first :: rest, strain = some p.2.suit) :
    strain = some (trickWinner strain first rest).2.suit ∧
      ∀ p ∈ first :: rest, strain = some p.2.suit →
        p.2.rank ≤ (trickWinner strain first rest).2.rank :=
  (winnerInv strain first rest).trump h

/-- If no trump was played, the trick is won by the highest card of the suit led. -/
theorem winner_highest_of_suit_led {strain : Strain} {first : Seat × Card}
    {rest : List (Seat × Card)} (h : ∀ p ∈ first :: rest, strain ≠ some p.2.suit) :
    (trickWinner strain first rest).2.suit = first.2.suit ∧
      ∀ p ∈ first :: rest, p.2.suit = first.2.suit →
        p.2.rank ≤ (trickWinner strain first rest).2.rank :=
  (winnerInv strain first rest).noTrump h

/-- In notrump, the trick is always won by the highest card of the suit led. -/
theorem winner_notrump (first : Seat × Card) (rest : List (Seat × Card)) :
    (trickWinner none first rest).2.suit = first.2.suit ∧
      ∀ p ∈ first :: rest, p.2.suit = first.2.suit →
        p.2.rank ≤ (trickWinner none first rest).2.rank :=
  winner_highest_of_suit_led (fun _ _ => by simp)

end Bridge
