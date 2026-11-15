-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bignum_BigNum_addqtvc: a verification condition for adding two
-- arbitrary-base integer digit lists, preserving validity and the represented
-- numeric sum. This file contains no proof.

{-# OPTIONS --safe #-}

module bignum_BigNum_addqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module BigNumTheory
  (base : Int)
  (base-def : oneZ <Z base)
  (Digit Num : Set)
  (digitDefault : Digit)
  (numDefault : Num)
  where

  listValue : List Int → Int
  listValue [] = zeroZ
  listValue (d ∷ rest) =
    addInt d (multiplyInt base (listValue rest))

  valid : List Int → Set
  valid [] = ⊤
  valid (d ∷ []) = (zeroZ <Z d) ∧ (d <Z base)
  valid (d ∷ next ∷ rest) =
    ((zeroZ ≤Z d) ∧ (d <Z base)) ∧
    valid (next ∷ rest)

  resultAntecedent : List Int → List Int → List Int → Set
  resultAntecedent n1 n2 result =
    valid result ∧
    (listValue result ≡
      addInt (addInt (listValue n1) (listValue n2)) zeroZ)

  resultConclusion : List Int → List Int → List Int → Set
  resultConclusion n1 n2 result =
    valid result ∧
    (listValue result ≡ addInt (listValue n1) (listValue n2))

  AddVC : List Int → List Int → Set
  AddVC n1 n2 =
    valid n1 →
    valid n2 →
    valid n1 ∧
    valid n2 ∧
    (zeroZ ≤Z zeroZ) ∧
    (zeroZ ≤Z oneZ) ∧
    ((result : List Int) →
      resultAntecedent n1 n2 result →
      resultConclusion n1 n2 result)

  add-vc : Set
  add-vc =
    (n1 n2 : List Int) →
    AddVC n1 n2
