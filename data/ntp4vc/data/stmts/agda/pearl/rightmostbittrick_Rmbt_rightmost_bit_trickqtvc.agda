-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/rightmostbittrick_Rmbt_rightmost_bit_trickqtvc: the 64-bit
-- rightmost-set-bit verification condition for x AND its two's-complement
-- negation. This file contains no proof.

{-# OPTIONS --safe #-}

module rightmostbittrick_Rmbt_rightmost_bit_trickqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤N_ _<N_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

_≤N_ : Nat → Nat → Set
m ≤N n = natLessOrEqual m n ≡ true

_<N_ : Nat → Nat → Set
m <N n = natLess m n ≡ true

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []V
replicate (suc n) value = value ∷V replicate n value

nthVec : {A : Set} {n : Nat} → A → Nat → Vec A n → A
nthVec default index []V = default
nthVec default zero (x ∷V xs) = x
nthVec default (suc index) (_ ∷V xs) =
  nthVec default index xs

notBit : Bool → Bool
notBit false = true
notBit true = false

andBit : Bool → Bool → Bool
andBit false _ = false
andBit true y = y

orBit : Bool → Bool → Bool
orBit false y = y
orBit true _ = true

xorBit : Bool → Bool → Bool
xorBit false y = y
xorBit true false = true
xorBit true true = false

andVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
andVec []V []V = []V
andVec (x ∷V xs) (y ∷V ys) =
  andBit x y ∷V andVec xs ys

differenceBit : Bool → Bool → Bool → Bool
differenceBit borrow x y =
  xorBit (xorBit x y) borrow

borrowBit : Bool → Bool → Bool → Bool
borrowBit borrow x y =
  orBit
    (andBit (notBit x) y)
    (andBit borrow (notBit (xorBit x y)))

subtractWithBorrow :
  {n : Nat} →
  Bool →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
subtractWithBorrow borrow []V []V = []V
subtractWithBorrow borrow (x ∷V xs) (y ∷V ys) =
  differenceBit borrow x y ∷V
  subtractWithBorrow (borrowBit borrow x y) xs ys

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

lowBit : Nat → Bool
lowBit zero = false
lowBit (suc zero) = true
lowBit (suc (suc n)) = lowBit n

natToVec : (width value : Nat) → Vec Bool width
natToVec zero value = []V
natToVec (suc width) value =
  lowBit value ∷V natToVec width (half value)

Word64 : Set
Word64 = Vec Bool 64

zeroWord64 sixtyFourWord64 : Word64
zeroWord64 = replicate 64 false
sixtyFourWord64 = natToVec 64 64

wordNegate : Word64 → Word64
wordNegate bits =
  subtractWithBorrow false zeroWord64 bits

rightmostBit : Word64 → Word64
rightmostBit bits =
  andVec bits (wordNegate bits)

bitAt : Word64 → Nat → Bool
bitAt bits index =
  nthVec false index bits

wordLess : Word64 → Word64 → Set
wordLess left right =
  unsignedNat left <N unsignedNat right

equalSubrange :
  Word64 →
  Word64 →
  Nat →
  Nat →
  Set
equalSubrange left right start length =
  (index : Nat) →
  (start ≤N index ∧ index <N (start + length)) →
  bitAt left index ≡ bitAt right index

equalSubrangeBV :
  Word64 →
  Word64 →
  Word64 →
  Word64 →
  Set
equalSubrangeBV left right start length =
  equalSubrange
    left
    right
    (unsignedNat start)
    (unsignedNat length)

RightmostBitTrickPost :
  Word64 →
  Word64 →
  Set
RightmostBitTrickPost x p-bv =
  let
    p = unsignedNat p-bv
    r = rightmostBit x
  in
  (zero ≤N p ∧ p <N 64)
  ∧ equalSubrange x zeroWord64 zero p
  ∧ bitAt x p ≡ true
  ∧ equalSubrange r zeroWord64 zero p
  ∧ equalSubrange
      r
      zeroWord64
      (p + 1)
      (natSubtract 63 p)
  ∧ bitAt r p ≡ true

rightmost-bit-trick'vc : Set
rightmost-bit-trick'vc =
  (x : Word64) →
  Not (x ≡ zeroWord64) →
  Not (x ≡ zeroWord64)
  ∧
  ((p-bv : Word64) →
    (wordLess p-bv sixtyFourWord64
     ∧ equalSubrangeBV x zeroWord64 zeroWord64 p-bv
     ∧ bitAt x (unsignedNat p-bv) ≡ true) →
    RightmostBitTrickPost x p-bv)
