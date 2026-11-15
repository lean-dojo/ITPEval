-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/euler002_Solve_fqtvc: the Euler problem 2 verification condition for
-- initializing and advancing the sum of even Fibonacci numbers up to a
-- nonnegative integer bound. This file contains no proof.

{-# OPTIONS --safe #-}

module euler002_Solve_fqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
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

natEven : Nat → Bool
natEven zero = true
natEven (suc zero) = false
natEven (suc (suc n)) = natEven n

intEven : Int → Bool
intEven (pos n) = natEven n
intEven (negsuc n) = natEven (suc n)

EvenZ : Int → Set
EvenZ x = intEven x ≡ true

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

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4

record Euler002Structure : Set where
  field
    fib : Int → Int
    fib-sum-even : Int → Int → Int

    fib-definition :
      (n : Int) →
      zeroZ ≤Z n →
      IfSet
        (intEqual n zeroZ)
        (fib n ≡ zeroZ)
        (IfSet
          (intEqual n oneZ)
          (fib n ≡ oneZ)
          (fib n ≡
            addInt
              (fib (subtractInt n oneZ))
              (fib (subtractInt n twoZ))))

    sum-zero :
      (m : Int) →
      fib-sum-even m zeroZ ≡ zeroZ

    sum-even-le :
      (n m : Int) →
      zeroZ ≤Z n →
      fib n ≤Z m →
      EvenZ (fib n) →
      fib-sum-even m (addInt n oneZ) ≡
      addInt (fib-sum-even m n) (fib n)

    sum-even-gt :
      (n m : Int) →
      zeroZ ≤Z n →
      m <Z fib n →
      EvenZ (fib n) →
      fib-sum-even m (addInt n oneZ) ≡
      fib-sum-even m n

    sum-odd :
      (n m : Int) →
      zeroZ ≤Z n →
      Not (EvenZ (fib n)) →
      fib-sum-even m (addInt n oneZ) ≡
      fib-sum-even m n

open Euler002Structure

fib-even : Euler002Structure → Int → Int
fib-even signature n =
  fib signature (multiplyInt threeZ n)

LoopStep :
  Euler002Structure →
  Int →
  Set
LoopStep signature m =
  (k n : Int) →
  zeroZ ≤Z n
  ∧ zeroZ ≤Z k
  ∧ fib-even signature n ≡ fib signature k
  ∧ fib-even signature (addInt n oneZ)
      ≡ fib signature (addInt k threeZ)
  ∧ zeroZ ≤Z fib-even signature n
  ∧ fib-even signature n
      <Z fib-even signature (addInt n oneZ) →
  IfSet
    (intLessOrEqual (fib-even signature n) m)
    (((zeroZ ≤Z subtractInt m (fib-even signature n))
      ∧
      (subtractInt m (fib-even signature (addInt n oneZ))
        <Z subtractInt m (fib-even signature n)))
    ∧ zeroZ ≤Z addInt n oneZ
    ∧ zeroZ ≤Z addInt k threeZ
    ∧ fib-even signature (addInt n oneZ)
        ≡ fib signature (addInt k threeZ)
    ∧ addInt
        (multiplyInt
          fourZ
          (fib-even signature (addInt n oneZ)))
        (fib-even signature n)
        ≡ fib-even signature (addInt (addInt n oneZ) oneZ)
    ∧ addInt
        (multiplyInt
          fourZ
          (fib-even signature (addInt n oneZ)))
        (fib-even signature n)
        ≡ fib signature (addInt (addInt k threeZ) threeZ)
    ∧ addInt
        (fib-sum-even signature m k)
        (fib-even signature n)
        ≡ fib-sum-even signature m (addInt k threeZ)
    ∧ zeroZ ≤Z fib-even signature (addInt n oneZ)
    ∧ fib-even signature (addInt n oneZ)
        <Z
        addInt
          (multiplyInt
            fourZ
            (fib-even signature (addInt n oneZ)))
          (fib-even signature n))
    (Exists Int
      (λ n1 →
        fib-sum-even signature m k
          ≡ fib-sum-even signature m n1
        ∧ m <Z fib signature n1))

SolveVC :
  Euler002Structure →
  Int →
  Set
SolveVC signature m =
  zeroZ ≤Z m →
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z zeroZ
  ∧ zeroZ ≡ fib-even signature zeroZ
  ∧ zeroZ ≡ fib signature zeroZ
  ∧ twoZ ≡ fib-even signature (addInt zeroZ oneZ)
  ∧ twoZ ≡ fib signature (addInt zeroZ threeZ)
  ∧ zeroZ ≡ fib-sum-even signature m zeroZ
  ∧ zeroZ ≤Z zeroZ
  ∧ zeroZ <Z twoZ
  ∧ LoopStep signature m

euler002-Solve-fqtvc : Set
euler002-Solve-fqtvc =
  (signature : Euler002Structure) →
  (m : Int) →
  SolveVC signature m
