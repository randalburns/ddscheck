/-!
# The rules of double-dummy bridge play

This is the trusted specification: every theorem in this project is about the
definitions in this file, so it is the one file a reader must check against the
rules of bridge. Nothing here depends on DDS or on the certificate format.
-/

namespace Bridge

inductive Suit | spades | hearts | diamonds | clubs
  deriving DecidableEq, Repr, Inhabited

/-- `none` is notrump. -/
abbrev Strain := Option Suit

/-- A higher `rank` is a stronger card; only the order of ranks matters. -/
structure Card where
  suit : Suit
  rank : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Seat | north | east | south | west
  deriving DecidableEq, Repr, Inhabited

/-- Play proceeds clockwise. -/
def Seat.next : Seat → Seat
  | .north => .east | .east => .south | .south => .west | .west => .north

inductive Side | ns | ew
  deriving DecidableEq, Repr, Inhabited

def Seat.side : Seat → Side
  | .north | .south => .ns
  | .east | .west => .ew

structure Hands where
  north : List Card
  east : List Card
  south : List Card
  west : List Card
  deriving DecidableEq, Repr, Inhabited

def Hands.get (h : Hands) : Seat → List Card
  | .north => h.north | .east => h.east | .south => h.south | .west => h.west

/-- Take a card out of one seat's hand. -/
def Hands.remove (h : Hands) (seat : Seat) (c : Card) : Hands :=
  let out := fun (l : List Card) => l.filter (· != c)
  match seat with
  | .north => { h with north := out h.north }
  | .east => { h with east := out h.east }
  | .south => { h with south := out h.south }
  | .west => { h with west := out h.west }

structure State where
  hands : Hands
  /-- Cards played to the current trick, in the order played. -/
  trick : List (Seat × Card)
  /-- Whose turn it is to play. -/
  turn : Seat
  deriving DecidableEq, Repr, Inhabited

/-- Lead anything; afterwards follow the suit led if able. -/
def legal (s : State) : List Card :=
  let hand := s.hands.get s.turn
  match s.trick with
  | [] => hand
  | (_, led) :: _ =>
    let following := hand.filter (·.suit == led.suit)
    if following.isEmpty then hand else following

/-- Does `a` take over from `best`, the card currently winning the trick? A higher
card of the same suit does; a card of another suit does only if it is a trump. -/
def beats (strain : Strain) (a best : Card) : Bool :=
  if a.suit == best.suit then decide (best.rank < a.rank)
  else strain == some a.suit

/-- The winning play of a trick, given its first play and the plays after it. -/
def trickWinner (strain : Strain) (first : Seat × Card) (rest : List (Seat × Card)) :
    Seat × Card :=
  rest.foldl (fun best p => if beats strain p.2 best.2 then p else best) first

/-- Play card `c`. Returns the next state and, if this card completed a trick,
the seat that won it (who also leads next). -/
def step (strain : Strain) (s : State) (c : Card) : State × Option Seat :=
  let hands := s.hands.remove s.turn c
  let trick := s.trick ++ [(s.turn, c)]
  match trick with
  | [p₁, p₂, p₃, p₄] =>
    let w := (trickWinner strain p₁ [p₂, p₃, p₄]).1
    ({ hands, trick := [], turn := w }, some w)
  | _ => ({ hands, trick, turn := s.turn.next }, none)

/-- One if this outcome is a trick for North-South. -/
def nsPoint : Option Seat → Nat
  | some w => if w.side = .ns then 1 else 0
  | none => 0

def maxOf : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxOf xs)

def minOf : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: ys => min x (minOf (y :: ys))

/-- The double-dummy value: tricks North-South take from now on when, with all
cards visible, North-South maximize and East-West minimize that number. `fuel` is
the number of cards still to be played. -/
def value (strain : Strain) : (fuel : Nat) → State → Nat
  | 0, _ => 0
  | fuel + 1, s =>
    let outcomes := (legal s).map fun c =>
      let r := step strain s c
      nsPoint r.2 + value strain fuel r.1
    match s.turn.side with
    | .ns => maxOf outcomes
    | .ew => minOf outcomes

def Hands.cards (h : Hands) : List Card := h.north ++ h.east ++ h.south ++ h.west

/-- A full deal: thirteen cards each, and every one of the 52 cards exactly once. -/
def validDeal (h : Hands) : Prop :=
  h.north.length = 13 ∧ h.east.length = 13 ∧ h.south.length = 13 ∧ h.west.length = 13 ∧
  h.cards.Nodup ∧ h.cards.all (fun c => decide (2 ≤ c.rank ∧ c.rank ≤ 14)) = true

/-- The start of play, with `leader` on lead. -/
def start (h : Hands) (leader : Seat) : State := { hands := h, trick := [], turn := leader }

/-- **The quantity DDS computes**: tricks for North-South from the opening lead. -/
def nsTricks (strain : Strain) (h : Hands) (leader : Seat) : Nat :=
  value strain 52 (start h leader)

end Bridge
