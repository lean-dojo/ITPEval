-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/compare_Compare_wmpn_cmpqtvc: the verification
-- condition for comparing two equal-length multiprecision unsigned integers
-- limb by limb and returning the comparison of their represented values.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module compare_Compare_wmpn_cmpqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

notBool : Bool → Bool
notBool false = true
notBool true = false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

zeroZ oneZ minusOneZ : Int
zeroZ = pos 0
oneZ = pos 1
minusOneZ = negsuc 0

min32 max32 radixZ : Int
min32 = negsuc 2147483647
max32 = pos 2147483647
radixZ = pos 18446744073709551616

int32InBounds : Int → Set
int32InBounds n = min32 ≤Z n ∧ n ≤Z max32

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

unsignedZ : {n : Nat} → Vec Bool n → Int
unsignedZ bits = pos (unsignedNat bits)

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

record Ptr (Zone A : Set) : Set where
  constructor pointer
  field
    memory    : Int → A
    cellCount : Nat
    off       : Int
    lo        : Int
    hi        : Int
    writeable : Bool
    region    : Zone

open Ptr public

pelts : {Zone : Set} → Ptr Zone Word64 → Int → Word64
pelts p = memory p

plength : {Zone : Set} → Ptr Zone Word64 → Int
plength p = pos (cellCount p)

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

valueFrom :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Nat →
  Int
valueFrom p index zero = zeroZ
valueFrom p index (suc count) =
  addInt
    (unsignedZ (pelts p index))
    (multiplyInt
      radixZ
      (valueFrom p (addInt index oneZ) count))

value :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Int
value p size =
  valueFrom p (off p) (intToNat size)

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

compareInt : Int → Int → Int
compareInt x y =
  ifInt
    (intLess x y)
    minusOneZ
    (ifInt (intEqual x y) zeroZ oneZ)

RangeEqual :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Set
RangeEqual x y lower upper =
  (j : Int) →
  (lower ≤Z j ∧ j <Z upper) →
  pelts x (addInt (off x) j) ≡
  pelts y (addInt (off y) j)

ComparisonResult :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int
ComparisonResult x y size =
  compareInt (value x size) (value y size)

AddressValid :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Set
AddressValid p index =
  lo p ≤Z addInt (off p) (signed32 index)
  ∧ addInt (off p) (signed32 index) <Z hi p

ContinueInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Set
ContinueInvariant x y size i previous =
  signed32 previous <Z signed32 i
  ∧ (zeroZ ≤Z signed32 previous
     ∧ signed32 previous ≤Z signed32 size)
  ∧ RangeEqual x y (signed32 previous) (signed32 size)

LimbDecision :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Set
LimbDecision x y size i previous lx ly =
  (equal-flag : Bool) →
  ((unsignedZ lx ≡ unsignedZ ly → equal-flag ≡ true)
   ∧
   (equal-flag ≡ true → lx ≡ ly)) →
  IfSet
    (notBool equal-flag)
    (IfSet
      (intLess (unsignedZ ly) (unsignedZ lx))
      (oneZ ≡ ComparisonResult x y (signed32 size))
      (minusOneZ ≡ ComparisonResult x y (signed32 size)))
    (ContinueInvariant x y size i previous)

IndexObligation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Set
IndexObligation x y size i previous =
  AddressValid x previous
  ∧
  let lx = pelts x (addInt (off x) (signed32 previous))
  in
  AddressValid y previous
  ∧
  let ly = pelts y (addInt (off y) (signed32 previous))
  in
  LimbDecision x y size i previous lx ly

DecrementObligation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
DecrementObligation x y size i =
  int32InBounds (subtractInt (signed32 i) oneZ)
  ∧
  ((previous : Word32) →
    signed32 previous ≡ subtractInt (signed32 i) oneZ →
    IndexObligation x y size i previous)

LoopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
LoopStep x y size i =
  ((zeroZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 size)
   ∧
   RangeEqual x y (signed32 i) (signed32 size)) →
  IfSet
    (intLessOrEqual oneZ (signed32 i))
    (DecrementObligation x y size i)
    (zeroZ ≡ ComparisonResult x y (signed32 size))

wmpn-cmp'vc : Set₁
wmpn-cmp'vc =
  (Zone : Set) →
  (x : Ptr Zone Word64) →
  (size : Word32) →
  (y : Ptr Zone Word64) →
  valid x (signed32 size) →
  valid y (signed32 size) →
  zeroZ ≤Z signed32 size
  ∧ signed32 size ≤Z signed32 size
  ∧ RangeEqual x y (signed32 size) (signed32 size)
  ∧ ((i : Word32) → LoopStep x y size i)
