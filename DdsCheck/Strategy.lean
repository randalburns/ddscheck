import DdsCheck.Checker

/-!
# What `value` means, in terms of strategies

`value` is defined with `maxOf` and `minOf`. This file states what that is supposed to mean
without using either of them: lines of play, strategies, and tricks counted along a line.
It then proves that `value` is exactly the number both sides can guarantee.

To review this, read the definitions down to `EWCanHold` and the final theorems. If `value`
had maximizing and minimizing the wrong way round, these theorems would be false.
-/

namespace Bridge

/-! ## Lines of play, strategies and guarantees -/

/-- `cards` is a complete line of play from `s`: each card is legal when played, and play
stops only when `n` cards have been played or nobody can play. -/
def IsLine (strain : Strain) : Nat → State → List Card → Prop
  | 0, _, cards => cards = []
  | _ + 1, s, [] => legal s = []
  | n + 1, s, c :: cards => c ∈ legal s ∧ IsLine strain n (step strain s c).1 cards

/-- The tricks North-South win along a line of play. -/
def tricksOf (strain : Strain) : State → List Card → Nat
  | _, [] => 0
  | s, c :: cards => nsPoint (step strain s c).2 + tricksOf strain (step strain s c).1 cards

/-- A strategy chooses a card from everything known: the cards played so far, oldest first,
and the current position. So strategies may depend on the history of the play. -/
abbrev Strategy := List Card → State → Card

/-- A strategy may only choose legal cards. -/
def Strategy.Valid (σ : Strategy) : Prop :=
  ∀ history s, legal s ≠ [] → σ history s ∈ legal s

/-- The same strategy, after card `c` has been played. -/
def Strategy.after (σ : Strategy) (c : Card) : Strategy := fun history s => σ (c :: history) s

/-- On each of `side`'s turns in this line, `side` played the card the strategy chose. -/
def Follows (strain : Strain) (side : Side) : Strategy → State → List Card → Prop
  | _, _, [] => True
  | σ, s, c :: cards =>
    (s.turn.side = side → c = σ [] s) ∧ Follows strain side (σ.after c) (step strain s c).1 cards

/-- North-South have a strategy that wins at least `t` tricks whatever East-West do. -/
def NSCanTake (strain : Strain) (n : Nat) (s : State) (t : Nat) : Prop :=
  ∃ σ : Strategy, σ.Valid ∧ ∀ cards, IsLine strain n s cards → Follows strain .ns σ s cards →
    t ≤ tricksOf strain s cards

/-- East-West have a strategy that holds North-South to at most `t` tricks whatever they do. -/
def EWCanHold (strain : Strain) (n : Nat) (s : State) (t : Nat) : Prop :=
  ∃ σ : Strategy, σ.Valid ∧ ∀ cards, IsLine strain n s cards → Follows strain .ew σ s cards →
    tricksOf strain s cards ≤ t

/-! ## An optimal strategy, built from `value` -/

/-- The result of playing `c`, according to `value`. -/
def outcomeOf (strain : Strain) (n : Nat) (s : State) (c : Card) : Nat :=
  nsPoint (step strain s c).2 + value strain n (step strain s c).1

def pickMax (f : Card → Nat) : List Card → Card
  | [] => default
  | [c] => c
  | c :: d :: ds =>
    let b := pickMax f (d :: ds)
    if f b ≤ f c then c else b

def pickMin (f : Card → Nat) : List Card → Card
  | [] => default
  | [c] => c
  | c :: d :: ds =>
    let b := pickMin f (d :: ds)
    if f c ≤ f b then c else b

theorem pickMax_spec (f : Card → Nat) {l : List Card} (h : l ≠ []) :
    pickMax f l ∈ l ∧ f (pickMax f l) = maxOf (l.map f) := by
  induction l with
  | nil => exact absurd rfl h
  | cons c cs ih =>
    cases cs with
    | nil => simp [pickMax, maxOf]
    | cons d ds =>
      obtain ⟨h1, h2⟩ := ih (by simp)
      simp only [pickMax]
      simp only [List.map_cons, maxOf] at h2 ⊢
      split
      · refine ⟨by simp, ?_⟩
        omega
      · refine ⟨List.mem_cons_of_mem _ h1, ?_⟩
        omega

theorem pickMin_spec (f : Card → Nat) {l : List Card} (h : l ≠ []) :
    pickMin f l ∈ l ∧ f (pickMin f l) = minOf (l.map f) := by
  induction l with
  | nil => exact absurd rfl h
  | cons c cs ih =>
    cases cs with
    | nil => simp [pickMin, minOf]
    | cons d ds =>
      obtain ⟨h1, h2⟩ := ih (by simp)
      simp only [pickMin]
      simp only [List.map_cons, minOf] at h2 ⊢
      split
      · refine ⟨by simp, ?_⟩
        omega
      · refine ⟨List.mem_cons_of_mem _ h1, ?_⟩
        omega

/-- The best card for `side` with `n` cards left. -/
def bestCard (strain : Strain) (side : Side) : Nat → State → Card
  | 0, s => pickMax (fun _ => 0) (legal s)
  | n + 1, s =>
    match side with
    | .ns => pickMax (outcomeOf strain n s) (legal s)
    | .ew => pickMin (outcomeOf strain n s) (legal s)

/-- Play the best card. The history is used only to count how many cards are left. -/
def optimal (strain : Strain) (side : Side) : Nat → Strategy
  | n, [], s => bestCard strain side n s
  | 0, _ :: _, s => bestCard strain side 0 s
  | n + 1, _ :: history, s => optimal strain side n history s

theorem bestCard_legal (strain : Strain) (side : Side) (n : Nat) {s : State} (h : legal s ≠ []) :
    bestCard strain side n s ∈ legal s := by
  cases n with
  | zero => exact (pickMax_spec _ h).1
  | succ n =>
    cases side
    · exact (pickMax_spec _ h).1
    · exact (pickMin_spec _ h).1

theorem optimal_valid (strain : Strain) (side : Side) (n : Nat) : (optimal strain side n).Valid := by
  intro history s h
  induction history generalizing n with
  | nil => simpa [optimal] using bestCard_legal strain side n h
  | cons c cs ih =>
    cases n with
    | zero => simpa [optimal] using bestCard_legal strain side 0 h
    | succ n => simpa [optimal] using ih n

theorem optimal_after (strain : Strain) (side : Side) (n : Nat) (c : Card) :
    (optimal strain side (n + 1)).after c = optimal strain side n := by
  funext history s
  rfl

theorem value_no_moves {strain : Strain} {n : Nat} {s : State} (h : legal s = []) :
    value strain (n + 1) s = 0 := by
  simp only [value, h, List.map_nil]
  cases s.turn.side <;> rfl

theorem outcomes_eq (strain : Strain) (n : Nat) (s : State) :
    outcomes strain n s = (legal s).map (outcomeOf strain n s) := rfl

/-- Playing `optimal` as North-South wins at least `value` tricks on every line. -/
theorem optimal_ns (strain : Strain) (n : Nat) (s : State) (cards : List Card)
    (hl : IsLine strain n s cards) (hf : Follows strain .ns (optimal strain .ns n) s cards) :
    value strain n s ≤ tricksOf strain s cards := by
  induction n generalizing s cards with
  | zero => simp [value]
  | succ n ih =>
    cases cards with
    | nil =>
      have : legal s = [] := hl
      rw [value_no_moves this]
      exact Nat.zero_le _
    | cons c cs =>
      obtain ⟨hc, hl'⟩ := hl
      obtain ⟨hturn, hf'⟩ := hf
      rw [optimal_after] at hf'
      have hrest := ih _ _ hl' hf'
      have hne : legal s ≠ [] := by
        intro he; rw [he] at hc; simp at hc
      have hgoal : tricksOf strain s (c :: cs)
          = nsPoint (step strain s c).2 + tricksOf strain (step strain s c).1 cs := rfl
      rw [hgoal]
      cases hs : s.turn.side with
      | ns =>
        have hpick : c = pickMax (outcomeOf strain n s) (legal s) := hturn hs
        rw [value_succ_ns hs, outcomes_eq, ← (pickMax_spec (outcomeOf strain n s) hne).2, ← hpick]
        simp only [outcomeOf]
        omega
      | ew =>
        rw [value_succ_ew hs]
        have := minOf_le (mem_outcomes (strain := strain) (n := n) hc)
        omega

/-- Playing `optimal` as East-West holds North-South to at most `value` tricks on every line. -/
theorem optimal_ew (strain : Strain) (n : Nat) (s : State) (cards : List Card)
    (hl : IsLine strain n s cards) (hf : Follows strain .ew (optimal strain .ew n) s cards) :
    tricksOf strain s cards ≤ value strain n s := by
  induction n generalizing s cards with
  | zero =>
    have : cards = [] := hl
    subst this
    simp [tricksOf]
  | succ n ih =>
    cases cards with
    | nil => simp [tricksOf]
    | cons c cs =>
      obtain ⟨hc, hl'⟩ := hl
      obtain ⟨hturn, hf'⟩ := hf
      rw [optimal_after] at hf'
      have hrest := ih _ _ hl' hf'
      have hne : legal s ≠ [] := by
        intro he; rw [he] at hc; simp at hc
      have hgoal : tricksOf strain s (c :: cs)
          = nsPoint (step strain s c).2 + tricksOf strain (step strain s c).1 cs := rfl
      rw [hgoal]
      cases hs : s.turn.side with
      | ew =>
        have hpick : c = pickMin (outcomeOf strain n s) (legal s) := hturn hs
        rw [value_succ_ew hs, outcomes_eq, ← (pickMin_spec (outcomeOf strain n s) hne).2, ← hpick]
        simp only [outcomeOf]
        omega
      | ns =>
        rw [value_succ_ns hs]
        have := le_maxOf (mem_outcomes (strain := strain) (n := n) hc)
        omega

/-! ## Playing two strategies against each other -/

/-- The line of play when North-South follow `σ` and East-West follow `τ`. -/
def playout (strain : Strain) : Nat → Strategy → Strategy → State → List Card
  | 0, _, _, _ => []
  | n + 1, σ, τ, s =>
    match legal s with
    | [] => []
    | _ :: _ =>
      let c := match s.turn.side with
        | .ns => σ [] s
        | .ew => τ [] s
      c :: playout strain n (σ.after c) (τ.after c) (step strain s c).1

theorem Strategy.Valid.after {σ : Strategy} (h : σ.Valid) (c : Card) : (σ.after c).Valid :=
  fun history s hs => h (c :: history) s hs

/-- Any two legal strategies produce a complete line that follows both. In particular, a
guarantee is never true just because no line of play exists. -/
theorem playout_spec (strain : Strain) (n : Nat) (σ τ : Strategy) (s : State)
    (hσ : σ.Valid) (hτ : τ.Valid) :
    IsLine strain n s (playout strain n σ τ s) ∧
      Follows strain .ns σ s (playout strain n σ τ s) ∧
      Follows strain .ew τ s (playout strain n σ τ s) := by
  induction n generalizing σ τ s with
  | zero => exact ⟨rfl, trivial, trivial⟩
  | succ n ih =>
    cases hl : legal s with
    | nil =>
      simp only [playout, hl]
      exact ⟨hl, trivial, trivial⟩
    | cons d ds =>
      have hne : legal s ≠ [] := by simp [hl]
      simp only [playout, hl]
      cases hs : s.turn.side with
      | ns =>
        obtain ⟨h1, h2, h3⟩ := ih (σ.after (σ [] s)) (τ.after (σ [] s)) (step strain s (σ [] s)).1
          (hσ.after _) (hτ.after _)
        refine ⟨⟨hl ▸ hσ [] s hne, h1⟩, ⟨fun _ => rfl, h2⟩, ⟨?_, h3⟩⟩
        intro he; rw [hs] at he; cases he
      | ew =>
        obtain ⟨h1, h2, h3⟩ := ih (σ.after (τ [] s)) (τ.after (τ [] s)) (step strain s (τ [] s)).1
          (hσ.after _) (hτ.after _)
        refine ⟨⟨hl ▸ hτ [] s hne, h1⟩, ⟨?_, h2⟩, ⟨fun _ => rfl, h3⟩⟩
        intro he; rw [hs] at he; cases he

/-! ## The theorems -/

/-- North-South can guarantee `t` tricks **exactly when** `t ≤ value`. -/
theorem nsCanTake_iff (strain : Strain) (n : Nat) (s : State) (t : Nat) :
    NSCanTake strain n s t ↔ t ≤ value strain n s := by
  constructor
  · rintro ⟨σ, hσ, hguar⟩
    have hτ := optimal_valid strain .ew n
    obtain ⟨h1, h2, h3⟩ := playout_spec strain n σ (optimal strain .ew n) s hσ hτ
    exact Nat.le_trans (hguar _ h1 h2) (optimal_ew strain n s _ h1 h3)
  · intro h
    exact ⟨optimal strain .ns n, optimal_valid strain .ns n,
      fun cards hl hf => Nat.le_trans h (optimal_ns strain n s cards hl hf)⟩

/-- East-West can hold North-South to `t` tricks **exactly when** `value ≤ t`. -/
theorem ewCanHold_iff (strain : Strain) (n : Nat) (s : State) (t : Nat) :
    EWCanHold strain n s t ↔ value strain n s ≤ t := by
  constructor
  · rintro ⟨τ, hτ, hguar⟩
    have hσ := optimal_valid strain .ns n
    obtain ⟨h1, h2, h3⟩ := playout_spec strain n (optimal strain .ns n) τ s hσ hτ
    exact Nat.le_trans (optimal_ns strain n s _ h1 h2) (hguar _ h1 h3)
  · intro h
    exact ⟨optimal strain .ew n, optimal_valid strain .ew n,
      fun cards hl hf => Nat.le_trans (optimal_ew strain n s cards hl hf) h⟩

/-- `value` is the one number that North-South can guarantee and East-West can hold them to. -/
theorem value_eq_iff (strain : Strain) (n : Nat) (s : State) (k : Nat) :
    value strain n s = k ↔ NSCanTake strain n s k ∧ EWCanHold strain n s k := by
  rw [nsCanTake_iff, ewCanHold_iff]
  omega

/-- **What every generated theorem means.** `nsTricks strain h leader = k` says exactly that
North-South have a strategy winning at least `k` tricks against every defence, and East-West
have a strategy holding them to at most `k` against every line of play. -/
theorem nsTricks_eq_iff (strain : Strain) (h : Hands) (leader : Seat) (k : Nat) :
    nsTricks strain h leader = k ↔
      NSCanTake strain 52 (start h leader) k ∧ EWCanHold strain 52 (start h leader) k :=
  value_eq_iff strain 52 (start h leader) k

end Bridge
