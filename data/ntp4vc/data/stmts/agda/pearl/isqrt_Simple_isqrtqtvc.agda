-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/isqrt_Simple_isqrtqtvc: the simple integer-square-root loop
-- verification condition for initialization, invariant preservation,
-- variant decrease, and the final square-root specification. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module isqrt_Simple_isqrtqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

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

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negativeNat n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

square : Int → Int
square x = multiplyInt x x

isqrtSpec : Int → Int → Set
isqrtSpec x result =
  zeroZ ≤Z result
  ∧ square result ≤Z x
  ∧ x <Z square (addInt result oneZ)

ContinueCase : Int → Int → Set
ContinueCase x count =
  let next = addInt count oneZ
  in
  (zeroZ ≤Z subtractInt x count
   ∧ subtractInt x next <Z subtractInt x count)
  ∧ zeroZ ≤Z next
  ∧ square next ≤Z x
  ∧ addInt
      (square next)
      (addInt (multiplyInt twoZ next) oneZ)
    ≡ square (addInt next oneZ)

LoopObligation : Int → Set
LoopObligation x =
  (count : Int) →
  (zeroZ ≤Z count ∧ square count ≤Z x) →
  IfSet
    (intLessOrEqual (square (addInt count oneZ)) x)
    (ContinueCase x count)
    (isqrtSpec x count)

isqrt'vc : Set
isqrt'vc =
  (x : Int) →
  zeroZ ≤Z x →
  zeroZ ≤Z zeroZ
  ∧ square zeroZ ≤Z x
  ∧ oneZ ≡ square (addInt zeroZ oneZ)
  ∧ LoopObligation x
