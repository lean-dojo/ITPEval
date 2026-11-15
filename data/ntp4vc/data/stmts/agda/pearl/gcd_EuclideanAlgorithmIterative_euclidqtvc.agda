-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/gcd_EuclideanAlgorithmIterative_euclidqtvc: an iterative Euclidean
-- algorithm verification condition preserving nonnegativity and the integer
-- greatest common divisor across a remainder step. This file contains no proof.

{-# OPTIONS --safe #-}

module gcd_EuclideanAlgorithmIterative_euclidqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

IfNat : Bool → Nat → Nat → Nat
IfNat true when-true when-false = when-true
IfNat false when-true when-false = when-false

natModFuel : Nat → Nat → Nat → Nat
natModFuel zero dividend divisor = dividend
natModFuel (suc fuel) dividend zero = dividend
natModFuel (suc fuel) dividend (suc divisor) =
  IfNat
    (natLess dividend (suc divisor))
    dividend
    (natModFuel fuel (natSubtract dividend (suc divisor)) (suc divisor))

natMod : Nat → Nat → Nat
natMod dividend divisor =
  natModFuel (suc dividend) dividend divisor

natGcdFuel : Nat → Nat → Nat → Nat
natGcdFuel zero a b = a
natGcdFuel (suc fuel) a zero = a
natGcdFuel (suc fuel) a (suc b) =
  natGcdFuel fuel (suc b) (natMod a (suc b))

natGcd : Nat → Nat → Nat
natGcd a b = natGcdFuel (suc b) a b

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

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

truncatedRemainder : Int → Int → Int
truncatedRemainder (pos dividend) divisor =
  pos (natMod dividend (absoluteNat divisor))
truncatedRemainder (negsuc dividend) divisor =
  negative (natMod (suc dividend) (absoluteNat divisor))

gcdInt : Int → Int → Int
gcdInt a b = pos (natGcd (absoluteNat a) (absoluteNat b))

zeroZ : Int
zeroZ = pos zero

EuclideanStep : Int → Int → Int → Int → Set
EuclideanStep u0 v0 v u =
  ((zeroZ ≤Z u ∧ zeroZ ≤Z v) ∧
   gcdInt u v ≡ gcdInt u0 v0) →
  IfSet
    (notBool (intEqual v zeroZ))
    (v ≠ zeroZ
     ∧ (zeroZ ≤Z v ∧ truncatedRemainder u v <Z v)
     ∧ (zeroZ ≤Z v ∧ zeroZ ≤Z truncatedRemainder u v)
     ∧ gcdInt v (truncatedRemainder u v) ≡ gcdInt u0 v0)
    (u ≡ gcdInt u0 v0)

euclid'vc : Set
euclid'vc =
  (u0 v0 : Int) →
  zeroZ ≤Z u0 →
  zeroZ ≤Z v0 →
  zeroZ ≤Z u0
  ∧ zeroZ ≤Z v0
  ∧ ((v u : Int) → EuclideanStep u0 v0 v u)
