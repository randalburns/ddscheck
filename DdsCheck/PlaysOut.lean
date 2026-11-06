import DdsCheck.RulesProps
import DdsCheck.Strategy

/-!
# On a valid deal, 52 plays is the whole game

`nsTricks` and `IsLine` stop after 52 cards. This file proves that is exactly when the game
ends: no line stops early because someone has no card to play, and when a line finishes,
every hand is empty and the table is clear. So the limit of 52 never cuts a game short.
-/

namespace Bridge

/-- Every seat is reached by going clockwise from any other. -/
theorem seat_cover (t x : Seat) :
    x = t ∨ x = t.next ∨ x = t.next.next ∨ x = t.next.next.next := by
  cases t <;> cases x <;> simp [Seat.next]

theorem seat_next_ne (t : Seat) :
    t.next ≠ t ∧ t.next.next ≠ t ∧ t.next.next.next ≠ t ∧ t.next.next.next.next = t := by
  cases t <;> simp [Seat.next]

/-- Hand sizes part-way through a trick, with `L` cards in the hand of the player to move.
The players who have already played to this trick each hold one card fewer. -/
structure Balanced (n : Nat) (s : State) (L : Nat) : Prop where
  nodup : ∀ x, (s.hands.get x).Nodup
  count : n + s.trick.length = 4 * L
  short : s.trick.length ≤ 3
  len0 : (s.hands.get s.turn).length = L
  len1 : (s.hands.get s.turn.next).length + min 1 (s.trick.length - 2) = L
  len2 : (s.hands.get s.turn.next.next).length + min 1 (s.trick.length - 1) = L
  len3 : (s.hands.get s.turn.next.next.next).length + min 1 s.trick.length = L

theorem length_filter_ne {l : List Card} {c : Card} (hn : l.Nodup) (hc : c ∈ l) :
    (l.filter (· != c)).length + 1 = l.length := by
  induction l with
  | nil => simp at hc
  | cons y ys ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hy : y = c
    · subst hy
      have hall : ys.filter (· != y) = ys := by
        rw [List.filter_eq_self]
        intro x hx
        have : x ≠ y := fun e => hn'.1 (e ▸ hx)
        simpa using this
      simp [hall]
    · have hin : c ∈ ys := by
        rcases List.mem_cons.mp hc with rfl | h
        · exact absurd rfl hy
        · exact h
      have := ih hn'.2 hin
      simp [hy]
      omega

theorem get_remove_self (h : Hands) (seat : Seat) (c : Card) :
    (h.remove seat c).get seat = (h.get seat).filter (· != c) := by
  cases seat <;> rfl

theorem legal_ne_nil {s : State} (h : s.hands.get s.turn ≠ []) : legal s ≠ [] := by
  unfold legal
  split
  · exact h
  · simp only
    split
    · exact h
    · rename_i hne
      intro he
      simp [he] at hne

theorem mem_hand_of_legal (s : State) {c : Card} (h : c ∈ legal s) : c ∈ s.hands.get s.turn :=
  legal_mem_hand s h

/-- Playing a legal card keeps the hands balanced, with one card fewer to play. -/
theorem balanced_step (strain : Strain) {n : Nat} {s : State} {L : Nat} {c : Card}
    (hb : Balanced (n + 1) s L) (hc : c ∈ legal s) :
    ∃ L', Balanced n (step strain s c).1 L' := by
  have hmem := mem_hand_of_legal s hc
  have hself : ((step strain s c).1.hands.get s.turn).length + 1
      = (s.hands.get s.turn).length := by
    rw [step_hands, get_remove_self]
    exact length_filter_ne (hb.nodup _) hmem
  have hother : ∀ x, x ≠ s.turn → (step strain s c).1.hands.get x = s.hands.get x :=
    fun x hx => play_keeps_other_hands strain s c hx
  have hnodup : ∀ x, ((step strain s c).1.hands.get x).Nodup := by
    intro x
    by_cases hx : x = s.turn
    · subst hx
      rw [step_hands, get_remove_self]
      exact (hb.nodup _).filter _
    · rw [hother x hx]
      exact hb.nodup x
  obtain ⟨hn1, hn2, hn3, hn4⟩ := seat_next_ne s.turn
  have e1 := hother _ hn1
  have e2 := hother _ hn2
  have e3 := hother _ hn3
  have h0 := hb.len0
  have h1 := hb.len1
  have h2 := hb.len2
  have h3 := hb.len3
  have hk := hb.short
  have hcount := hb.count
  by_cases hlt : s.trick.length < 3
  · obtain ⟨ht, hturn, _⟩ := step_continue strain s c hlt
    have hlen : (step strain s c).1.trick.length = s.trick.length + 1 := by simp [ht]
    refine ⟨L, hnodup, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [hturn, e1]; omega
    · rw [hturn, hlen, e2]; omega
    · rw [hturn, hlen, e3]; omega
    · rw [hturn, hn4, hlen]; omega
  · have hexists : ∃ p₁ p₂ p₃, s.trick = [p₁, p₂, p₃] := by
      have h3len : s.trick.length = 3 := by omega
      generalize s.trick = t at h3len
      match t, h3len with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    obtain ⟨p₁, p₂, p₃, htr⟩ := hexists
    obtain ⟨ht, hturn, _⟩ := step_complete strain s c htr
    simp only [htr, List.length_cons, List.length_nil] at h1 h2 h3 hcount
    have hall : ∀ x, ((step strain s c).1.hands.get x).length + 1 = L := by
      intro x
      rcases seat_cover s.turn x with rfl | rfl | rfl | rfl
      · omega
      · rw [e1]; omega
      · rw [e2]; omega
      · rw [e3]; omega
    refine ⟨L - 1, hnodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht]; simp; omega
    · rw [ht]; simp
    · have := hall (step strain s c).1.turn; omega
    · rw [ht]; have := hall (step strain s c).1.turn.next; simp; omega
    · rw [ht]; have := hall (step strain s c).1.turn.next.next; simp; omega
    · rw [ht]; have := hall (step strain s c).1.turn.next.next.next; simp; omega

/-- The position after playing a list of cards. -/
def afterPlay (strain : Strain) : State → List Card → State
  | s, [] => s
  | s, c :: cards => afterPlay strain (step strain s c).1 cards

/-- From a balanced position, every line plays all `n` cards and ends balanced with none left. -/
theorem balanced_line (strain : Strain) (n : Nat) (s : State) (L : Nat) (cards : List Card)
    (hb : Balanced n s L) (hl : IsLine strain n s cards) :
    cards.length = n ∧ ∃ L', Balanced 0 (afterPlay strain s cards) L' := by
  induction n generalizing s L cards with
  | zero =>
    have hnil : cards = [] := hl
    subst hnil
    exact ⟨rfl, L, hb⟩
  | succ n ih =>
    cases cards with
    | nil =>
      have hempty : legal s = [] := hl
      have hne : s.hands.get s.turn ≠ [] := by
        intro he
        have h0 := hb.len0
        have hcount := hb.count
        have hk := hb.short
        rw [he] at h0
        simp at h0
        omega
      exact absurd hempty (legal_ne_nil hne)
    | cons c cs =>
      obtain ⟨hc, hrest⟩ := hl
      obtain ⟨L', hb'⟩ := balanced_step strain hb hc
      obtain ⟨hlen, hend⟩ := ih _ L' cs hb' hrest
      exact ⟨by simp [hlen], hend⟩

/-- With no cards left to play, every hand is empty and the table is clear. -/
theorem balanced_zero {s : State} {L : Nat} (hb : Balanced 0 s L) :
    s.trick = [] ∧ ∀ x, s.hands.get x = [] := by
  have hcount := hb.count
  have hk := hb.short
  have hL : L = 0 := by omega
  have hlen0 : s.trick.length = 0 := by omega
  refine ⟨List.length_eq_zero_iff.mp hlen0, ?_⟩
  intro x
  apply List.length_eq_zero_iff.mp
  have h0 := hb.len0
  have h1 := hb.len1
  have h2 := hb.len2
  have h3 := hb.len3
  rcases seat_cover s.turn x with rfl | rfl | rfl | rfl <;> omega

theorem validDeal_nodup {h : Hands} (hv : validDeal h) (x : Seat) : (h.get x).Nodup := by
  obtain ⟨_, _, _, _, hnd, _⟩ := hv
  simp only [Hands.cards, List.nodup_append] at hnd
  cases x <;> simp only [Hands.get] <;> grind

theorem validDeal_balanced {h : Hands} (hv : validDeal h) (leader : Seat) :
    Balanced 52 (start h leader) 13 := by
  have hnd := validDeal_nodup hv
  obtain ⟨hn, he, hs, hw, _⟩ := hv
  have hlen : ∀ x, (h.get x).length = 13 := by
    intro x
    cases x <;> assumption
  refine ⟨hnd, by simp [start], by simp [start], hlen _, ?_, ?_, ?_⟩ <;> simp [start, hlen]

/-- **On a valid deal, every line of play has exactly 52 cards and uses up the deal:** nobody
is ever left unable to play, and at the end all four hands are empty and the table is clear. -/
theorem valid_deal_plays_out (strain : Strain) {h : Hands} (hv : validDeal h) (leader : Seat)
    (cards : List Card) (hl : IsLine strain 52 (start h leader) cards) :
    cards.length = 52 ∧ (afterPlay strain (start h leader) cards).trick = [] ∧
      ∀ x, (afterPlay strain (start h leader) cards).hands.get x = [] := by
  obtain ⟨hlen, L, hb⟩ := balanced_line strain 52 _ 13 cards (validDeal_balanced hv leader) hl
  exact ⟨hlen, balanced_zero hb⟩

end Bridge
