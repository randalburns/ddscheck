import DdsCheck.Canon

/-!
# The certificate checker and its soundness

A certificate is a list of proved *facts*, each building only on earlier ones. A fact
says "from this position, this side can take at least `need` more tricks", and comes
with a strategy tree for the coming trick: one card on that side's turns, and an
answer to every legal card on the opponents' turns.

`checkClaim_sound` is the theorem everything rests on. It holds for *every*
certificate, so whatever produced the certificate need not be trusted.
-/

namespace Bridge

/-- Tricks still to be completed, with `n` cards unplayed. -/
def rem (n : Nat) (s : State) : Nat := (n + s.trick.length) / 4

/-- `side` can take at least `t` more tricks. For East-West this is phrased as an upper
bound on North-South, since `value` counts North-South's tricks. -/
def Goal (strain : Strain) : Side → Nat → State → Nat → Prop
  | .ns, n, s, t => t ≤ value strain n s
  | .ew, n, s, t => value strain n s + t ≤ rem n s

/-- One if this outcome is a trick for `side`. -/
def won (side : Side) : Option Seat → Nat
  | some w => if w.side = side then 1 else 0
  | none => 0

/-! ### Facts about `maxOf` and `minOf` -/

theorem le_maxOf {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ maxOf l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hin
    · simp [maxOf]; omega
    · have := ih hin; simp [maxOf]; omega

theorem maxOf_le {l : List Nat} {b : Nat} (h : ∀ x ∈ l, x ≤ b) : maxOf l ≤ b := by
  induction l with
  | nil => simp [maxOf]
  | cons y ys ih =>
    have h1 := h y (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    simp [maxOf]; omega

theorem minOf_le {l : List Nat} {x : Nat} (h : x ∈ l) : minOf l ≤ x := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    cases ys with
    | nil => simp at h; subst h; simp [minOf]
    | cons z zs =>
      rcases List.mem_cons.mp h with rfl | hin
      · simp [minOf]; omega
      · have := ih hin; simp [minOf]; omega

theorem le_minOf {l : List Nat} {k : Nat} (hne : l ≠ []) (h : ∀ x ∈ l, k ≤ x) : k ≤ minOf l := by
  induction l with
  | nil => simp at hne
  | cons y ys ih =>
    cases ys with
    | nil => simpa [minOf] using h y (by simp)
    | cons z zs =>
      have h1 := h y (by simp)
      have h2 := ih (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp [minOf]; omega

/-! ### One step of play -/

/-- The list of results `value` takes the max or min of. -/
def outcomes (strain : Strain) (n : Nat) (s : State) : List Nat :=
  (legal s).map fun c => nsPoint (step strain s c).2 + value strain n (step strain s c).1

theorem value_succ_ns {strain : Strain} {n : Nat} {s : State} (h : s.turn.side = .ns) :
    value strain (n + 1) s = maxOf (outcomes strain n s) := by
  simp only [value, h, outcomes]

theorem value_succ_ew {strain : Strain} {n : Nat} {s : State} (h : s.turn.side = .ew) :
    value strain (n + 1) s = minOf (outcomes strain n s) := by
  simp only [value, h, outcomes]

theorem side_cases (side : Side) : side = .ns ∨ side = .ew := by cases side <;> simp

/-- A step either continues the trick or completes it from three cards on the table. -/
theorem step_cases (strain : Strain) (s : State) (c : Card) :
    ((step strain s c).2 = none ∧ (step strain s c).1.trick.length = s.trick.length + 1) ∨
    (∃ w, (step strain s c).2 = some w ∧ (step strain s c).1.trick = [] ∧ s.trick.length = 3) := by
  have hlen : (s.trick ++ [(s.turn, c)]).length = s.trick.length + 1 := by simp
  unfold step
  simp only
  revert hlen
  generalize s.trick ++ [(s.turn, c)] = t
  intro hlen
  split
  · right
    simp at hlen
    exact ⟨_, rfl, rfl, by omega⟩
  · left
    exact ⟨rfl, hlen⟩

theorem value_le_rem (strain : Strain) (n : Nat) (s : State) :
    value strain n s ≤ rem n s := by
  induction n generalizing s with
  | zero => simp [value]
  | succ n ih =>
    have hall : ∀ x ∈ outcomes strain n s, x ≤ rem (n + 1) s := by
      intro x hx
      simp only [outcomes, List.mem_map] at hx
      obtain ⟨c, _, rfl⟩ := hx
      have hv := ih (step strain s c).1
      rcases step_cases strain s c with ⟨h2, h1⟩ | ⟨w, h2, h1, h3⟩
      · simp only [rem, h2, nsPoint, h1] at hv ⊢
        have : (n + (s.trick.length + 1)) = n + 1 + s.trick.length := by omega
        rw [this] at hv
        omega
      · simp only [rem, h2, nsPoint, h1, h3, List.length_nil] at hv ⊢
        split <;> omega
    rcases side_cases s.turn.side with h | h
    · rw [value_succ_ns h]; exact maxOf_le hall
    · rw [value_succ_ew h]
      cases hl : outcomes strain n s with
      | nil => simp [minOf]
      | cons y ys =>
        exact Nat.le_trans (minOf_le (by simp)) (hall y (by simp [hl]))

theorem goal_zero (strain : Strain) (side : Side) (n : Nat) (s : State) : Goal strain side n s 0 := by
  cases side
  · simp [Goal]
  · simpa [Goal] using value_le_rem strain n s

theorem goal_mono {strain : Strain} {side : Side} {n : Nat} {s : State} {t u : Nat}
    (h : Goal strain side n s u) (hle : t ≤ u) : Goal strain side n s t := by
  cases side <;> simp only [Goal] at h ⊢ <;> omega

theorem goal_canon {strain : Strain} {side : Side} {n : Nat} {s : State} {t : Nat}
    (h : Goal strain side n (canon s) t) : Goal strain side n s t := by
  have hlen : (canon s).trick.length = s.trick.length := by
    simp [canon, mapState]
  cases side <;> simp only [Goal, rem, value_canon, hlen] at h ⊢ <;> omega

/-- From the next position's goal, the outcome of a card is at least the need here. -/
theorem outcome_ns {strain : Strain} {n : Nat} {s : State} {c : Card} {t : Nat}
    (h : Goal strain .ns n (step strain s c).1 (t - won .ns (step strain s c).2)) :
    t ≤ nsPoint (step strain s c).2 + value strain n (step strain s c).1 := by
  simp only [Goal] at h
  cases hw : (step strain s c).2 with
  | none => simp only [hw, won, nsPoint] at h ⊢; omega
  | some w => simp only [hw, won, nsPoint] at h ⊢; split at h <;> simp_all <;> omega

/-- The same for East-West: the outcome leaves North-South within the bound. -/
theorem outcome_ew {strain : Strain} {n : Nat} {s : State} {c : Card} {t : Nat}
    (h : Goal strain .ew n (step strain s c).1 (t - won .ew (step strain s c).2)) :
    nsPoint (step strain s c).2 + value strain n (step strain s c).1 + t ≤ rem (n + 1) s := by
  simp only [Goal] at h
  have hle := value_le_rem strain n (step strain s c).1
  rcases step_cases strain s c with ⟨h2, h1⟩ | ⟨w, h2, h1, h3⟩
  · simp only [h2, won, nsPoint, rem, h1] at h ⊢
    have : (n + (s.trick.length + 1)) = n + 1 + s.trick.length := by omega
    rw [this] at h
    omega
  · simp only [h2, won, nsPoint, rem, h1, h3, List.length_nil, Nat.add_zero] at h hle ⊢
    have h4 : (n + 1 + 3) / 4 = n / 4 + 1 := by omega
    rw [h4]
    cases hs : w.side <;> simp [hs] at h ⊢ <;> omega

/-! ### Certificates -/

/-- The strategy for one fact. Below a `ref`, an earlier fact takes over. -/
inductive Tree where
  /-- Use earlier fact number `i`. -/
  | ref (i : Nat)
  /-- The proving side plays this card. -/
  | pick (c : Card) (next : Tree)
  /-- The opponents move: one subtree for each legal card, in order. -/
  | each (children : Array Tree)
  deriving Inhabited

structure Fact where
  state : State
  side : Side
  need : Nat
  fuel : Nat
  deriving Inhabited

def Fact.Valid (strain : Strain) (f : Fact) : Prop := Goal strain f.side f.fuel f.state f.need

/-- `f c i` holds for every element `c` at its position `i`. -/
def allIdx (f : Card → Nat → Bool) : List Card → Nat → Bool
  | [], _ => true
  | c :: cs, i => f c i && allIdx f cs (i + 1)

theorem allIdx_sound {f : Card → Nat → Bool} {l : List Card} {i : Nat}
    (h : allIdx f l i = true) : ∀ c ∈ l, ∃ j, f c j = true := by
  induction l generalizing i with
  | nil => simp
  | cons y ys ih =>
    simp only [allIdx, Bool.and_eq_true] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hin
    · exact ⟨i, h.1⟩
    · exact ih h.2 c hin

/-- Check a strategy tree against the goal `t` for `side`. -/
def walk (strain : Strain) (table : Array Fact) (side : Side) :
    Nat → Tree → State → Nat → Bool
  | 0, _, _, t => t == 0
  | n + 1, tree, s, t =>
    if t = 0 then true else
    match tree with
    | .ref i =>
      match table[i]? with
      | none => false
      | some f => f.side == side && f.fuel == n + 1 && decide (t ≤ f.need) && f.state == canon s
    | .pick c next =>
      s.turn.side == side && (legal s).contains c &&
        walk strain table side n next (step strain s c).1 (t - won side (step strain s c).2)
    | .each kids =>
      s.turn.side != side && !(legal s).isEmpty &&
        allIdx (fun c i =>
          walk strain table side n (kids.getD i (.ref 0)) (step strain s c).1
            (t - won side (step strain s c).2)) (legal s) 0

theorem outcomes_ne_nil {strain : Strain} {n : Nat} {s : State} (h : (legal s).isEmpty = false) :
    outcomes strain n s ≠ [] := by
  simp only [outcomes]
  intro hnil
  rw [List.map_eq_nil_iff] at hnil
  simp [hnil] at h

theorem mem_outcomes {strain : Strain} {n : Nat} {s : State} {c : Card} (h : c ∈ legal s) :
    nsPoint (step strain s c).2 + value strain n (step strain s c).1 ∈ outcomes strain n s :=
  List.mem_map.mpr ⟨c, h, rfl⟩

/-- Accepted strategy trees are correct. -/
theorem walk_sound {strain : Strain} {table : Array Fact}
    (htable : ∀ f ∈ table, f.Valid strain) {side : Side} (n : Nat) (tree : Tree) (s : State)
    (t : Nat) (h : walk strain table side n tree s t = true) : Goal strain side n s t := by
  induction n generalizing tree s t with
  | zero =>
    simp only [walk, beq_iff_eq] at h
    subst h
    exact goal_zero strain side 0 s
  | succ n ih =>
    by_cases ht : t = 0
    · subst ht; exact goal_zero strain side _ s
    · simp only [walk, ht, ↓reduceIte] at h
      cases tree with
      | ref i =>
        simp only at h
        cases hi : table[i]? with
        | none => simp [hi] at h
        | some f =>
          simp only [hi, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
          have hmem : f ∈ table := by
            obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hi
            exact heq ▸ Array.getElem_mem hlt
          have hv : Goal strain f.side f.fuel f.state f.need := htable f hmem
          rw [h1, h2, h4] at hv
          exact goal_canon (goal_mono hv h3)
      | pick c next =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        have hnext := ih next _ _ h3
        have hmem := mem_outcomes (strain := strain) (n := n) h2
        cases side with
        | ns =>
          rw [Goal, value_succ_ns h1]
          exact Nat.le_trans (outcome_ns hnext) (le_maxOf hmem)
        | ew =>
          rw [Goal, value_succ_ew h1]
          have h5 := outcome_ew hnext
          have h6 := minOf_le hmem
          omega
      | each kids =>
        simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        have hkids : ∀ c ∈ legal s, Goal strain side n (step strain s c).1
            (t - won side (step strain s c).2) := by
          intro c hc
          obtain ⟨j, hj⟩ := allIdx_sound h3 c hc
          exact ih _ _ _ hj
        cases side with
        | ns =>
          have hturn : s.turn.side = .ew := by
            cases hs : s.turn.side <;> simp_all
          rw [Goal, value_succ_ew hturn]
          apply le_minOf (outcomes_ne_nil h2)
          intro x hx
          simp only [outcomes, List.mem_map] at hx
          obtain ⟨c, hc, rfl⟩ := hx
          exact outcome_ns (hkids c hc)
        | ew =>
          have hturn : s.turn.side = .ns := by
            cases hs : s.turn.side <;> simp_all
          rw [Goal, value_succ_ns hturn]
          have hne : ∃ c, c ∈ legal s := by
            cases hl : legal s with
            | nil => simp [hl] at h2
            | cons c cs => exact ⟨c, by simp⟩
          obtain ⟨c₀, hc₀⟩ := hne
          have hb := outcome_ew (hkids c₀ hc₀)
          have hmax : maxOf (outcomes strain n s) ≤ rem (n + 1) s - t := by
            apply maxOf_le
            intro x hx
            simp only [outcomes, List.mem_map] at hx
            obtain ⟨c, hc, rfl⟩ := hx
            have := outcome_ew (hkids c hc)
            omega
          omega

/-- One line of a certificate: a claimed fact and its strategy. -/
structure Entry where
  state : State
  side : Side
  need : Nat
  tree : Tree
  deriving Inhabited

def Entry.fuel (e : Entry) : Nat := e.state.hands.cards.length

def Entry.fact (e : Entry) : Fact :=
  { state := e.state, side := e.side, need := e.need, fuel := e.fuel }

/-- Check each entry in turn, adding it to the table of facts. -/
def run (strain : Strain) (table : Array Fact) : List Entry → Option (Array Fact)
  | [] => some table
  | e :: es =>
    if walk strain table e.side e.fuel e.tree e.state e.need then
      run strain (table.push e.fact) es
    else none

theorem run_sound {strain : Strain} {table result : Array Fact} {es : List Entry}
    (htable : ∀ f ∈ table, f.Valid strain) (h : run strain table es = some result) :
    ∀ f ∈ result, f.Valid strain := by
  induction es generalizing table with
  | nil =>
    simp only [run, Option.some.injEq] at h
    exact h ▸ htable
  | cons e es ih =>
    simp only [run] at h
    split at h
    · rename_i hw
      apply ih _ h
      intro f hf
      rcases Array.mem_push.mp hf with hin | rfl
      · exact htable f hin
      · exact walk_sound htable _ _ _ _ hw
    · simp at h

/-- Everything `ddscheck` verifies about one claim. -/
structure Claim where
  strain : Strain
  hands : Hands
  leader : Seat
  /-- The claimed number of tricks for North-South. -/
  nsTricks : Nat
  deriving Inhabited

instance (h : Hands) : Decidable (validDeal h) := by
  unfold validDeal; infer_instance

/-- Accept the claim if the entries prove a lower bound for each side that meet. -/
def checkClaim (claim : Claim) (entries : List Entry) (nsFact ewFact : Nat) : Bool :=
  let s := canon (start claim.hands claim.leader)
  decide (validDeal claim.hands) && decide (claim.nsTricks ≤ 13) &&
  match run claim.strain #[] entries with
  | none => false
  | some table =>
    match table[nsFact]?, table[ewFact]? with
    | some a, some b =>
      a.side == .ns && a.fuel == 52 && decide (claim.nsTricks ≤ a.need) && a.state == s &&
      b.side == .ew && b.fuel == 52 && decide (13 - claim.nsTricks ≤ b.need) && b.state == s
    | _, _ => false

/-- **Soundness.** For any certificate at all: if the checker accepts, the deal is valid
and the double-dummy value is exactly the claimed number of tricks. -/
theorem checkClaim_sound (claim : Claim) (entries : List Entry) (nsFact ewFact : Nat)
    (h : checkClaim claim entries nsFact ewFact = true) :
    validDeal claim.hands ∧
      nsTricks claim.strain claim.hands claim.leader = claim.nsTricks := by
  simp only [checkClaim, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hdeal, hle⟩, hrun⟩ := h
  refine ⟨hdeal, ?_⟩
  cases hr : run claim.strain #[] entries with
  | none => simp [hr] at hrun
  | some table =>
    simp only [hr] at hrun
    have hvalid := run_sound (strain := claim.strain) (table := #[]) (by simp) hr
    have hmem : ∀ {i : Nat} {f : Fact}, table[i]? = some f → f ∈ table := by
      intro i f hi
      obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hi
      exact heq ▸ Array.getElem_mem hlt
    split at hrun
    · rename_i a b ha hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrun
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hrun
      have va : Goal claim.strain a.side a.fuel a.state a.need := hvalid a (hmem ha)
      have vb : Goal claim.strain b.side b.fuel b.state b.need := hvalid b (hmem hb)
      rw [h1, h2, h4] at va
      rw [h5, h6, h8] at vb
      have ga : Goal claim.strain .ns 52 (start claim.hands claim.leader) claim.nsTricks :=
        goal_canon (goal_mono va h3)
      have gb : Goal claim.strain .ew 52 (start claim.hands claim.leader) (13 - claim.nsTricks) :=
        goal_canon (goal_mono vb h7)
      have hrem : rem 52 (start claim.hands claim.leader) = 13 := by
        simp [rem, start]
      simp only [Goal, hrem] at ga gb
      unfold Bridge.nsTricks
      omega
    · simp at hrun

end Bridge
