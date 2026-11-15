-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bignum_BigNum_add_digitqtvc: a verification condition for adding one
-- digit to an arbitrary-base integer digit list, preserving validity and the
-- represented numeric value. This file contains no proof.

{-# OPTIONS --safe #-}

module bignum_BigNum_add_digitqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

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

  tailMatches : List Int → List Int → Set
  tailMatches [] expected = ⊥
  tailMatches (_ ∷ actual) expected = actual ≡ expected

  safetyCondition : List Int → Int → Set
  safetyCondition [] d = ⊤
  safetyCondition n@(d₀ ∷ rest) d =
    Not (addInt d d₀ <Z base) →
    tailMatches n rest ∧
    valid rest ∧
    (zeroZ ≤Z oneZ) ∧
    (oneZ <Z base)

  resultAntecedent : List Int → Int → List Int → Set
  resultAntecedent [] d result =
    IfSet
      (intEqual d zeroZ)
      (result ≡ [])
      (result ≡ d ∷ [])
  resultAntecedent (d₀ ∷ rest) d result =
    IfSet
      (intLess (addInt d d₀) base)
      (result ≡ addInt d d₀ ∷ rest)
      (Exists
        (List Int)
        (λ outputTail →
          (valid outputTail ∧
           (listValue outputTail ≡
             addInt (listValue rest) oneZ)) ∧
          (result ≡
            subtractInt (addInt d d₀) base ∷ outputTail)))

  resultConclusion : List Int → Int → List Int → Set
  resultConclusion n d result =
    valid result ∧
    (listValue result ≡ addInt (listValue n) d)

  AddDigitVC : List Int → Int → Set
  AddDigitVC n d =
    valid n →
    (zeroZ ≤Z d) →
    (d <Z base) →
    safetyCondition n d ∧
    ((result : List Int) →
      resultAntecedent n d result →
      resultConclusion n d result)

  add-digit-vc : Set
  add-digit-vc =
    (n : List Int) →
    (d : Int) →
    AddDigitVC n d
