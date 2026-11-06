import DdsCheck.Checker

/-!
# Reading certificate files

Untrusted, and needs no proof: `checkClaim_sound` holds for whatever this produces, and a
theorem or verdict states its deal and claim separately from the certificate's entries.
-/

namespace Bridge.Format

open Bridge

structure Reader where
  bytes : ByteArray
  pos : Nat

abbrev Parse := StateT Reader (Except String)

def u8 : Parse Nat := do
  let r ← get
  if h : r.pos < r.bytes.size then
    set { r with pos := r.pos + 1 }
    return r.bytes[r.pos].toNat
  else throw "unexpected end of file"

partial def varint : Parse Nat := do
  let b ← u8
  if b < 128 then return b
  return (b - 128) + 128 * (← varint)

def suitOf : Nat → Except String Suit
  | 0 => pure .spades | 1 => pure .hearts | 2 => pure .diamonds | 3 => pure .clubs
  | n => throw s!"bad suit {n}"

def seatOf : Nat → Except String Seat
  | 0 => pure .north | 1 => pure .east | 2 => pure .south | 3 => pure .west
  | n => throw s!"bad seat {n}"

def card : Parse Card := do
  let b ← u8
  return { suit := ← suitOf (b / 16), rank := b % 16 }

def cardList : Parse (List Card) := do
  let n ← u8
  let mut acc : Array Card := Array.emptyWithCapacity n
  for _ in [0:n] do
    acc := acc.push (← card)
  return acc.toList

def hands : Parse Hands := do
  let north ← cardList
  let east ← cardList
  let south ← cardList
  let west ← cardList
  return { north, east, south, west }

partial def tree : Parse Tree := do
  match ← u8 with
  | 0 => return .ref (← varint)
  | 1 =>
    let c ← card
    return .pick c (← tree)
  | 2 =>
    let n ← u8
    let mut kids : Array Tree := Array.emptyWithCapacity n
    for _ in [0:n] do
      kids := kids.push (← tree)
    return .each kids
  | t => throw s!"bad tree tag {t}"

def entry : Parse Entry := do
  let hs ← hands
  let turn ← seatOf (← u8)
  let side : Side := if (← u8) == 0 then .ns else .ew
  let need ← u8
  let t ← tree
  return { state := { hands := hs, trick := [], turn }, side, need, tree := t }

structure Record where
  claim : Claim
  entries : List Entry
  nsFact : Nat
  ewFact : Nat

def record : Parse Record := do
  let s ← u8
  let strain : Strain ← if s == 4 then pure none else some <$> suitOf s
  let leader ← seatOf (← u8)
  let nsTricks ← u8
  let hs ← hands
  let n ← varint
  let mut es : Array Entry := Array.emptyWithCapacity n
  for _ in [0:n] do
    es := es.push (← entry)
  let nsFact ← varint
  let ewFact ← varint
  return { claim := { strain, hands := hs, leader, nsTricks }, entries := es.toList, nsFact, ewFact }

/-- Parse every record in a certificate file, with the offset where each begins. -/
partial def records (bytes : ByteArray) : Except String (Array (Nat × Record)) :=
  let rec go (r : Reader) (acc : Array (Nat × Record)) : Except String (Array (Nat × Record)) :=
    if r.pos < bytes.size then do
      let (rc, r') ← record.run r
      go r' (acc.push (r.pos, rc))
    else pure acc
  go { bytes, pos := 0 } #[]

def hexDigit (c : UInt8) : UInt8 :=
  if c < 58 then c - 48 else c - 87

/-- Decode the hexadecimal text form used to embed a certificate in a Lean source file. -/
def decodeHex (text : String) : ByteArray := Id.run do
  let raw := text.toUTF8
  let mut out := ByteArray.emptyWithCapacity (raw.size / 2)
  let mut i := 0
  while i + 1 < raw.size do
    out := out.push (hexDigit raw[i]! * 16 + hexDigit raw[i + 1]!)
    i := i + 2
  return out

/-- The record at a byte offset, or an empty one (which `checkClaim` rejects). -/
def recordAt (bytes : ByteArray) (offset : Nat) : Record :=
  match record.run { bytes, pos := offset } with
  | .ok (rc, _) => rc
  | .error _ => { claim := default, entries := [], nsFact := 0, ewFact := 0 }

end Bridge.Format
