-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sf_HoareLogic_factorialqtvc: the factorial-loop verification condition
-- using the recursive equations for factorial over unbounded integers. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module sf_HoareLogic_factorialqtvc where

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

record FactorialTheory : Set where
  field
    fact : Int → Int

    fact-zero :
      fact zeroZ ≡ oneZ

    fact-positive-step :
      (n : Int) →
      zeroZ <Z n →
      fact n ≡
        multiplyInt n (fact (subtractInt n oneZ))

open FactorialTheory using (fact)

FactorialVC : FactorialTheory → Int → Set
FactorialVC theory x =
  zeroZ ≤Z x →
  zeroZ ≤Z x
  ∧ multiplyInt oneZ (fact theory x) ≡ fact theory x
  ∧ ((z y : Int) →
      (zeroZ ≤Z z
       ∧ multiplyInt y (fact theory z) ≡ fact theory x) →
      IfSet
        (intEqual z zeroZ)
        (y ≡ fact theory x)
        ((zeroZ ≤Z z
          ∧ subtractInt z oneZ <Z z)
         ∧ zeroZ ≤Z subtractInt z oneZ
         ∧ multiplyInt
             (multiplyInt y z)
             (fact theory (subtractInt z oneZ))
           ≡ fact theory x))

factorial'vc : (theory : FactorialTheory) → Set
factorial'vc theory =
  (x : Int) →
  FactorialVC theory x
