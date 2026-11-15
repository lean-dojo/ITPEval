-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/euler001_Euler001_solveqtvc: the Euler problem 1 verification
-- condition equating the closed formula with the sum of positive multiples
-- of three or five below a positive integer. This file contains no proof.

{-# OPTIONS --safe #-}

module euler001_Euler001_solveqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

absoluteInt : Int → Int
absoluteInt (pos n) = pos n
absoluteInt (negsuc n) = pos (suc n)

zeroZ oneZ twoZ threeZ fiveZ fifteenZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fiveZ = pos 5
fifteenZ = pos 15

EuclideanDivision :
  Int →
  Int →
  Int →
  Int →
  Set
EuclideanDivision dividend divisor quotient remainder =
  dividend ≡
    addInt (multiplyInt divisor quotient) remainder
  ∧ zeroZ ≤Z remainder
  ∧ remainder <Z absoluteInt divisor

record Euler001Structure : Set where
  field
    quotient remainder : Int → Int → Int
    sum-multiple-3-5-lt : Int → Int

    division-law :
      (x y : Int) →
      zeroZ ≤Z x →
      zeroZ <Z y →
      EuclideanDivision
        x
        y
        (quotient x y)
        (remainder x y)

    sum-empty :
      sum-multiple-3-5-lt zeroZ ≡ zeroZ

    sum-no :
      (n : Int) →
      zeroZ ≤Z n →
      remainder n threeZ ≠ zeroZ →
      remainder n fiveZ ≠ zeroZ →
      sum-multiple-3-5-lt (addInt n oneZ) ≡
      sum-multiple-3-5-lt n

    sum-yes :
      (n : Int) →
      zeroZ ≤Z n →
      (remainder n threeZ ≡ zeroZ
       ∨ remainder n fiveZ ≡ zeroZ) →
      sum-multiple-3-5-lt (addInt n oneZ) ≡
      addInt (sum-multiple-3-5-lt n) n

open Euler001Structure

closedNumerator :
  Int →
  Int →
  Int →
  Int
closedNumerator n3 n5 n15 =
  subtractInt
    (addInt
      (multiplyInt
        (multiplyInt threeZ n3)
        (addInt n3 oneZ))
      (multiplyInt
        (multiplyInt fiveZ n5)
        (addInt n5 oneZ)))
    (multiplyInt
      (multiplyInt fifteenZ n15)
      (addInt n15 oneZ))

SolveVC : Euler001Structure → Int → Set
SolveVC signature n =
  oneZ ≤Z n →
  threeZ ≠ zeroZ
  ∧
  let n3 =
        quotient signature
          (subtractInt n oneZ)
          threeZ
  in
  fiveZ ≠ zeroZ
  ∧
  let n5 =
        quotient signature
          (subtractInt n oneZ)
          fiveZ
  in
  fifteenZ ≠ zeroZ
  ∧
  let n15 =
        quotient signature
          (subtractInt n oneZ)
          fifteenZ
  in
  twoZ ≠ zeroZ
  ∧ quotient signature
      (closedNumerator n3 n5 n15)
      twoZ
    ≡ sum-multiple-3-5-lt signature n

solve'vc : (signature : Euler001Structure) → Set
solve'vc signature =
  (n : Int) →
  SolveVC signature n
