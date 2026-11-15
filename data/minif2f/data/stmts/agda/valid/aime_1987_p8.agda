-- Statement-only formalization of miniF2F valid problem aime_1987_p8: 112 is the
-- greatest positive natural n for which a unique natural k makes n / (n + k)
-- lie strictly between 8 / 15 and 7 / 13. This file contains no proof.

module aime-1987-p8 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

NatLessOrEqual : Nat → Nat → Set
NatLessOrEqual m n = NatLess m (suc n)

record Fraction : Set where
  constructor fraction
  field
    numerator   : Nat
    denominator : Nat

FractionLess : Fraction → Fraction → Set
FractionLess x y =
  NatLess
    (Fraction.numerator x * Fraction.denominator y)
    (Fraction.numerator y * Fraction.denominator x)

ratio : Nat → Nat → Fraction
ratio n k = fraction n (n + k)

InInterval : Nat → Nat → Set
InInterval n k =
  FractionLess (fraction 8 15) (ratio n k) ∧
  FractionLess (ratio n k) (fraction 7 13)

record ExistsUnique (A : Set) (P : A → Set) : Set where
  constructor uniqueWitness
  field
    value      : A
    property   : P value
    uniqueness : (other : A) → P other → other ≡ value

Eligible : Nat → Set
Eligible n =
  NatLess zero n ∧
  ExistsUnique Nat (λ k → InInterval n k)

IsGreatest : (Nat → Set) → Nat → Set
IsGreatest predicate greatest =
  predicate greatest ∧
  ((n : Nat) → predicate n → NatLessOrEqual n greatest)

aime-1987-p8 : Set
aime-1987-p8 = IsGreatest Eligible 112
