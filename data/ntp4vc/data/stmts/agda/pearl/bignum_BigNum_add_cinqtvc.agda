-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bignum_BigNum_add_cinqtvc: a verification condition for adding two
-- arbitrary-base integer digit lists with an incoming carry, preserving
-- validity and the represented numeric value. This file contains no proof.

{-# OPTIONS --safe #-}

module bignum_BigNum_add_cinqtvc where

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

  safetyCondition : List Int → List Int → Int → Set
  safetyCondition [] [] cin =
    valid [] ∧
    (zeroZ ≤Z cin) ∧
    (cin <Z base)
  safetyCondition n1@(_ ∷ _) [] cin =
    valid n1 ∧
    (zeroZ ≤Z cin) ∧
    (cin <Z base)
  safetyCondition [] n2@(_ ∷ _) cin =
    valid n2 ∧
    (zeroZ ≤Z cin) ∧
    (cin <Z base)
  safetyCondition n1@(x2 ∷ x3) (x ∷ x1) cin =
    IfSet
      (intLess (addInt (addInt cin x2) x) base)
      (tailMatches n1 x3 ∧
       valid x3 ∧
       valid x1 ∧
       (zeroZ ≤Z zeroZ) ∧
       (zeroZ ≤Z oneZ))
      (tailMatches n1 x3 ∧
       valid x3 ∧
       valid x1 ∧
       (zeroZ ≤Z oneZ) ∧
       (oneZ ≤Z oneZ))

  resultAntecedent : List Int → List Int → Int → List Int → Set
  resultAntecedent [] [] cin result =
    valid result ∧
    (listValue result ≡ addInt (listValue []) cin)
  resultAntecedent n1@(_ ∷ _) [] cin result =
    valid result ∧
    (listValue result ≡ addInt (listValue n1) cin)
  resultAntecedent [] n2@(_ ∷ _) cin result =
    valid result ∧
    (listValue result ≡ addInt (listValue n2) cin)
  resultAntecedent (x2 ∷ x3) (x ∷ x1) cin result =
    let d = addInt (addInt cin x2) x
    in
    IfSet
      (intLess d base)
      (Exists
        (List Int)
        (λ o1 →
          (valid o1 ∧
           (listValue o1 ≡
             addInt
               (addInt (listValue x3) (listValue x1))
               zeroZ)) ∧
          (result ≡ d ∷ o1)))
      (Exists
        (List Int)
        (λ o1 →
          (valid o1 ∧
           (listValue o1 ≡
             addInt
               (addInt (listValue x3) (listValue x1))
               oneZ)) ∧
          (result ≡ subtractInt d base ∷ o1)))

  resultConclusion : List Int → List Int → Int → List Int → Set
  resultConclusion n1 n2 cin result =
    valid result ∧
    (listValue result ≡
      addInt (addInt (listValue n1) (listValue n2)) cin)

  AddCinVC : List Int → List Int → Int → Set
  AddCinVC n1 n2 cin =
    valid n1 →
    valid n2 →
    (zeroZ ≤Z cin) →
    (cin ≤Z oneZ) →
    safetyCondition n1 n2 cin ∧
    ((result : List Int) →
      resultAntecedent n1 n2 cin result →
      resultConclusion n1 n2 cin result)

  add-cin-vc : Set
  add-cin-vc =
    (n1 n2 : List Int) →
    (cin : Int) →
    AddCinVC n1 n2 cin
