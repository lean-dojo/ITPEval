-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/base_info_BaseInfo_wmpn_get_base_infoqtvc: the
-- verification condition for computing arbitrary-base multiprecision
-- information by repeated powers within unsigned 32- and 64-bit bounds.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module base_info_BaseInfo_wmpn_get_base_infoqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _*_; div-helper)

infix 4 _≠_ _≤N_ _<N_ _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

_≤N_ : Nat → Nat → Set
m ≤N n = natLessOrEqual m n ≡ true

_<N_ : Nat → Nat → Set
m <N n = natLess m n ≡ true

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

differenceInt : Nat → Nat → Int
differenceInt zero zero = pos zero
differenceInt (suc m) zero = pos (suc m)
differenceInt zero (suc n) = negsuc n
differenceInt (suc m) (suc n) = differenceInt m n

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

power : Nat → Nat → Nat
power base zero = 1
power base (suc exponent) = base * power base exponent

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsigned : {n : Nat} → Vec Bool n → Nat
unsigned []V = zero
unsigned (bit ∷V bits) =
  bitValue bit + 2 * unsigned bits

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

max32 max64 radix64 : Nat
max32 = 4294967295
max64 = 18446744073709551615
radix64 = suc max64

UInt32InBounds : Nat → Set
UInt32InBounds value = value ≤N max32

UInt64InBounds : Nat → Set
UInt64InBounds value = value ≤N max64

record WmpnBaseInfo : Set where
  constructor base-info
  field
    base        : Nat
    exponent    : Word32
    power-value : Word64

    base-lower :
      2 ≤N base
    base-upper :
      base ≤N 256
    power-below-radix :
      unsigned power-value <N radix64
    radix-bounded-by-next-power :
      radix64 ≤N unsigned power-value * base
    exponent-lower :
      7 ≤N unsigned exponent
    exponent-upper :
      unsigned exponent ≤N 63
    power-value-correct :
      unsigned power-value ≡ power base (unsigned exponent)

open WmpnBaseInfo

GrowthBranch :
  Word64 →
  Word64 →
  Word32 →
  Word64 →
  Set
GrowthBranch b1 m exp1 p =
  UInt64InBounds (unsigned p * unsigned b1)
  ∧
  ((o1 : Word64) →
    unsigned o1 ≡ unsigned p * unsigned b1 →
    UInt32InBounds (unsigned exp1 + 1)
    ∧
    ((o2 : Word32) →
      unsigned o2 ≡ unsigned exp1 + 1 →
      ((pos zero ≤Z differenceInt (unsigned m) (unsigned p))
       ∧
       (differenceInt (unsigned m) (unsigned o1)
        <Z differenceInt (unsigned m) (unsigned p)))
      ∧
      power (unsigned b1) (unsigned o2) ≡ unsigned o1
      ∧
      1 ≤N unsigned o2
      ∧
      unsigned o2 ≤N 64))

ExitInvariant :
  Word64 →
  Word32 →
  Word64 →
  Set
ExitInvariant b1 exp1 p =
  let base-value = unsigned b1
  in
  (2 ≤N base-value
   ∧
   base-value ≤N 256)
  ∧
  (unsigned p <N radix64
   ∧
   radix64 ≤N unsigned p * base-value)
  ∧
  (7 ≤N unsigned exp1
   ∧
   unsigned exp1 ≤N 63)
  ∧
  unsigned p ≡ power base-value (unsigned exp1)

ExitBranch :
  Word64 →
  Word32 →
  Word64 →
  Set
ExitBranch b1 exp1 p =
  ExitInvariant b1 exp1 p
  ∧
  ((result : WmpnBaseInfo) →
    base result ≡ unsigned b1
    ∧
    exponent result ≡ exp1
    ∧
    power-value result ≡ p →
    base result ≡ unsigned b1)

LoopStep :
  Word64 →
  Word64 →
  Word32 →
  Word64 →
  Set
LoopStep b1 m exp1 p =
  power (unsigned b1) (unsigned exp1) ≡ unsigned p
  ∧
  1 ≤N unsigned exp1
  ∧
  unsigned exp1 ≤N 64 →
  IfSet
    (natLessOrEqual (unsigned p) (unsigned m))
    (GrowthBranch b1 m exp1 p)
    (ExitBranch b1 exp1 p)

QuotientBody : Word64 → Word64 → Set
QuotientBody b1 m =
  (power (unsigned b1) 1 ≡ unsigned b1
   ∧
   1 ≤N 1
   ∧
   1 ≤N 64)
  ∧
  ((exp1 : Word32) →
    (p : Word64) →
    LoopStep b1 m exp1 p)

wmpn-get-base-info'vc : Set
wmpn-get-base-info'vc =
  (b1 : Word64) →
  2 ≤N unsigned b1 →
  unsigned b1 ≤N 256 →
  unsigned b1 ≠ zero
  ∧
  UInt64InBounds (natDivide max64 (unsigned b1))
  ∧
  ((m : Word64) →
    unsigned m ≡ natDivide max64 (unsigned b1) →
    QuotientBody b1 m)
