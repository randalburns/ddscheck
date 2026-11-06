import DdsCheck.Rules

/-!
# Only the relative order of ranks matters

If a map on cards keeps suits and keeps the order of ranks among the cards still
in play, it does not change the double-dummy value. In particular we may replace
every rank by its position among the remaining cards of its suit (`canon`), so a
certificate can share one proof between many positions.
-/

namespace Bridge

def mapHands (f : Card → Card) (h : Hands) : Hands :=
  { north := h.north.map f, east := h.east.map f, south := h.south.map f, west := h.west.map f }

def mapPlay (f : Card → Card) (p : Seat × Card) : Seat × Card := (p.1, f p.2)

def mapState (f : Card → Card) (s : State) : State :=
  { hands := mapHands f s.hands, trick := s.trick.map (mapPlay f), turn := s.turn }

/-- Every card still in play: in a hand or on the table. -/
def present (s : State) : List Card := s.hands.cards ++ s.trick.map (·.2)

/-- `f` keeps suits and keeps the order of ranks on the cards in `s`. -/
structure Faithful (f : Card → Card) (s : State) : Prop where
  suit : ∀ a ∈ present s, (f a).suit = a.suit
  rank : ∀ a ∈ present s, ∀ b ∈ present s, a.suit = b.suit →
    (a.rank < b.rank ↔ (f a).rank < (f b).rank)

theorem Faithful.eq_iff {f : Card → Card} {s : State} (h : Faithful f s)
    {a b : Card} (ha : a ∈ present s) (hb : b ∈ present s) : f a = f b ↔ a = b := by
  constructor
  · intro e
    have hs : a.suit = b.suit := by
      rw [← h.suit a ha, ← h.suit b hb, e]
    have h1 := h.rank a ha b hb hs
    have h2 := h.rank b hb a ha hs.symm
    rw [e] at h1 h2
    have hr : a.rank = b.rank := by omega
    cases a; cases b; simp_all
  · intro e; rw [e]

theorem mem_present_hand {s : State} {seat : Seat} {c : Card} (h : c ∈ s.hands.get seat) :
    c ∈ present s := by
  cases seat <;> simp_all [present, Hands.get, Hands.cards]

theorem mem_present_trick {s : State} {p : Seat × Card} (h : p ∈ s.trick) :
    p.2 ∈ present s := by
  simp only [present, List.mem_append, List.mem_map]
  exact Or.inr ⟨p, h, rfl⟩

theorem get_mapHands (f : Card → Card) (h : Hands) (seat : Seat) :
    (mapHands f h).get seat = (h.get seat).map f := by
  cases seat <;> rfl

theorem legal_subset (s : State) {c : Card} (h : c ∈ legal s) : c ∈ s.hands.get s.turn := by
  unfold legal at h
  split at h
  · exact h
  · simp only at h
    split at h
    · exact h
    · exact (List.mem_filter.mp h).1

theorem legal_map {f : Card → Card} {s : State} (hf : Faithful f s) :
    legal (mapState f s) = (legal s).map f := by
  unfold legal
  simp only [mapState, get_mapHands]
  cases ht : s.trick with
  | nil => simp
  | cons p ps =>
    have hp : p.2 ∈ present s := mem_present_trick (by simp [ht])
    have hfilter : ((s.hands.get s.turn).map f).filter (fun x => x.suit == (mapPlay f p).2.suit)
        = ((s.hands.get s.turn).filter (fun x => x.suit == p.2.suit)).map f := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro x hx
      have hxp := mem_present_hand hx
      simp [mapPlay, hf.suit x hxp, hf.suit p.2 hp]
    simp only [List.map_cons]
    rcases p with ⟨seat, led⟩
    simp only [] at hfilter
    simp only [hfilter]
    by_cases he : ((s.hands.get s.turn).filter (fun x => x.suit == led.suit)).isEmpty
    · simp [he]
    · simp [he]

theorem beats_map {f : Card → Card} {s : State} (hf : Faithful f s) (strain : Strain)
    {a b : Card} (ha : a ∈ present s) (hb : b ∈ present s) :
    beats strain (f a) (f b) = beats strain a b := by
  unfold beats
  rw [hf.suit a ha, hf.suit b hb]
  by_cases hs : a.suit = b.suit
  · simp only [hs, beq_self_eq_true, ite_true]
    have := hf.rank b hb a ha hs.symm
    simp only [decide_eq_decide]
    exact this.symm
  · have : (a.suit == b.suit) = false := by simpa using hs
    simp [this]

theorem foldl_winner_map {f : Card → Card} {s : State} (hf : Faithful f s) (strain : Strain)
    (rest : List (Seat × Card)) (hrest : ∀ p ∈ rest, p.2 ∈ present s) (best : Seat × Card)
    (hbest : best.2 ∈ present s) :
    (rest.map (mapPlay f)).foldl (fun b p => if beats strain p.2 b.2 then p else b)
        (mapPlay f best)
      = mapPlay f (rest.foldl (fun b p => if beats strain p.2 b.2 then p else b) best) := by
  induction rest generalizing best with
  | nil => rfl
  | cons p ps ih =>
    have hp : p.2 ∈ present s := hrest p (by simp)
    have hps : ∀ q ∈ ps, q.2 ∈ present s := fun q hq => hrest q (by simp [hq])
    simp only [List.map_cons, List.foldl_cons]
    have hb : beats strain (mapPlay f p).2 (mapPlay f best).2 = beats strain p.2 best.2 :=
      beats_map hf strain hp hbest
    rw [hb]
    by_cases hc : beats strain p.2 best.2 = true
    · simp only [hc, ite_true]
      exact ih hps p hp
    · simp only [hc]
      exact ih hps best hbest

theorem remove_map {f : Card → Card} {s : State} (hf : Faithful f s) {c : Card}
    (hc : c ∈ present s) (seat : Seat) :
    (mapHands f s.hands).remove seat (f c) = mapHands f (s.hands.remove seat c) := by
  have key : ∀ (l : List Card), (∀ x ∈ l, x ∈ present s) →
      (l.map f).filter (· != f c) = (l.filter (· != c)).map f := by
    intro l hl
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x hx
    have h := hf.eq_iff (hl x hx) hc
    have hb : (f x == f c) = (x == c) := by
      rw [Bool.eq_iff_iff]; simpa using h
    simp [bne, hb]
  have hn : ∀ x ∈ s.hands.north, x ∈ present s := fun x h => by
    simp [present, Hands.cards, h]
  have he : ∀ x ∈ s.hands.east, x ∈ present s := fun x h => by
    simp [present, Hands.cards, h]
  have hs : ∀ x ∈ s.hands.south, x ∈ present s := fun x h => by
    simp [present, Hands.cards, h]
  have hw : ∀ x ∈ s.hands.west, x ∈ present s := fun x h => by
    simp [present, Hands.cards, h]
  cases seat <;>
    simp only [Hands.remove, mapHands, key _ hn, key _ he, key _ hs, key _ hw]

theorem step_map {f : Card → Card} {s : State} (hf : Faithful f s) (strain : Strain)
    {c : Card} (hc : c ∈ present s) :
    step strain (mapState f s) (f c)
      = (mapState f (step strain s c).1, (step strain s c).2) := by
  have hrem := remove_map hf hc s.turn
  have htrick : ∀ p ∈ s.trick ++ [(s.turn, c)], p.2 ∈ present s := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact mem_present_trick h
    · simp at h; subst h; exact hc
  have hmapt : s.trick.map (mapPlay f) ++ [(s.turn, f c)]
      = (s.trick ++ [(s.turn, c)]).map (mapPlay f) := by
    simp [mapPlay]
  unfold step
  simp only [mapState, hrem, hmapt]
  revert htrick
  generalize s.trick ++ [(s.turn, c)] = t
  intro htrick
  match t, htrick with
  | [p₁, p₂, p₃, p₄], htrick =>
    have hw := foldl_winner_map hf strain [p₂, p₃, p₄]
      (fun q hq => htrick q (List.mem_cons_of_mem _ hq)) p₁ (htrick p₁ (by simp))
    have hw1 : (trickWinner strain (mapPlay f p₁)
        [mapPlay f p₂, mapPlay f p₃, mapPlay f p₄]).1
        = (trickWinner strain p₁ [p₂, p₃, p₄]).1 := by
      unfold trickWinner
      have := congrArg Prod.fst hw
      simpa [mapPlay] using this
    simp [hw1]
  | [], _ => simp
  | [_], _ => simp
  | [_, _], _ => simp
  | [_, _, _], _ => simp
  | _ :: _ :: _ :: _ :: _ :: _, _ => simp

theorem mem_cards_remove {h : Hands} {seat : Seat} {c x : Card}
    (hx : x ∈ (h.remove seat c).cards) : x ∈ h.cards := by
  cases seat <;>
    simp only [Hands.remove, Hands.cards, List.mem_append, List.mem_filter] at hx ⊢ <;> grind

/-- Every card still in play after a step was in play before it. -/
theorem present_step (strain : Strain) (s : State) {c x : Card} (hc : c ∈ present s)
    (hx : x ∈ present (step strain s c).1) : x ∈ present s := by
  have hsub : ∀ x, x ∈ (s.hands.remove s.turn c).cards → x ∈ present s := by
    intro x hx
    simp only [present, List.mem_append]
    exact Or.inl (mem_cards_remove hx)
  have htrick : ∀ p ∈ s.trick ++ [(s.turn, c)], p.2 ∈ present s := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact mem_present_trick h
    · simp at h; subst h; exact hc
  unfold step at hx
  simp only at hx
  revert hx htrick
  generalize s.trick ++ [(s.turn, c)] = t
  intro hx htrick
  split at hx
  · simp only [present, List.map_nil, List.append_nil] at hx
    exact hsub x hx
  · simp only [present, List.mem_append, List.mem_map] at hx
    rcases hx with h | ⟨p, hp, rfl⟩
    · exact hsub x h
    · exact htrick p hp

theorem Faithful.step {f : Card → Card} {s : State} (hf : Faithful f s) (strain : Strain)
    {c : Card} (hc : c ∈ present s) : Faithful f (step strain s c).1 where
  suit a ha := hf.suit a (present_step strain s hc ha)
  rank a ha b hb := hf.rank a (present_step strain s hc ha) b (present_step strain s hc hb)

/-- A faithful map leaves the double-dummy value unchanged. -/
theorem value_map (strain : Strain) (fuel : Nat) (f : Card → Card) (s : State)
    (hf : Faithful f s) : value strain fuel (mapState f s) = value strain fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    have houts : ((legal (mapState f s)).map fun c =>
          nsPoint (step strain (mapState f s) c).2 + value strain n (step strain (mapState f s) c).1)
        = (legal s).map fun c => nsPoint (step strain s c).2 + value strain n (step strain s c).1 := by
      rw [legal_map hf, List.map_map]
      apply List.map_congr_left
      intro c hc
      have hcp : c ∈ present s := mem_present_hand (legal_subset s hc)
      simp only [Function.comp, step_map hf strain hcp]
      rw [ih _ (hf.step strain hcp)]
    have hturn : (mapState f s).turn = s.turn := rfl
    simp only [value, hturn, houts]

/-! ### Canonical ranks -/

/-- The rank of `c` becomes the number of cards of its suit in `ps` below it. -/
def canonCard (ps : List Card) (c : Card) : Card :=
  { suit := c.suit, rank := ps.countP fun x => x.suit == c.suit && decide (x.rank < c.rank) }

def canon (s : State) : State := mapState (canonCard (present s)) s

theorem count_lt_of_lt (ps : List Card) {a b : Card} (hs : a.suit = b.suit)
    (hr : a.rank < b.rank) (ha : a ∈ ps) :
    (ps.countP fun x => x.suit == a.suit && decide (x.rank < a.rank))
      < ps.countP fun x => x.suit == b.suit && decide (x.rank < b.rank) := by
  induction ps with
  | nil => simp at ha
  | cons y ys ih =>
    have hle : (ys.countP fun x => x.suit == a.suit && decide (x.rank < a.rank))
        ≤ ys.countP fun x => x.suit == b.suit && decide (x.rank < b.rank) := by
      apply List.countP_mono_left
      intro x _ hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx ⊢
      exact ⟨hx.1.trans hs, by omega⟩
    rcases List.mem_cons.mp ha with rfl | hin
    · rw [List.countP_cons_of_neg (by simp), List.countP_cons_of_pos (by simp [hs, hr])]
      omega
    · have hih := ih hin
      by_cases h1 : (y.suit == a.suit && decide (y.rank < a.rank)) = true
      · have h2 : (y.suit == b.suit && decide (y.rank < b.rank)) = true := by
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 ⊢
          exact ⟨h1.1.trans hs, by omega⟩
        simp only [List.countP_cons]
        (repeat' split) <;> first | omega | contradiction
      · simp only [List.countP_cons]
        (repeat' split) <;> first | omega | contradiction

theorem count_le_of_le (ps : List Card) {a b : Card} (hs : a.suit = b.suit)
    (hr : a.rank ≤ b.rank) :
    (ps.countP fun x => x.suit == a.suit && decide (x.rank < a.rank))
      ≤ ps.countP fun x => x.suit == b.suit && decide (x.rank < b.rank) := by
  apply List.countP_mono_left
  intro x _ hx
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1.trans hs, by omega⟩

theorem faithful_canon (s : State) : Faithful (canonCard (present s)) s where
  suit _ _ := rfl
  rank a ha b _ hs := by
    constructor
    · intro h
      exact count_lt_of_lt (present s) hs h ha
    · intro h
      false_or_by_contra
      have := count_le_of_le (present s) hs.symm (show b.rank ≤ a.rank by omega)
      simp only [canonCard] at h
      omega

/-- **Rank canonicalization preserves the double-dummy value.** -/
theorem value_canon (strain : Strain) (fuel : Nat) (s : State) :
    value strain fuel (canon s) = value strain fuel s :=
  value_map strain fuel _ s (faithful_canon s)

end Bridge
