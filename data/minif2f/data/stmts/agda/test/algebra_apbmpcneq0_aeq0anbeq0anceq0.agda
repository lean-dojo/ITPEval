-- Statement-only formalization of miniF2F test artifact
-- algebra_apbmpcneq0_aeq0anbeq0anceq0 using rational Cauchy sequences for the
-- standard real numbers: a rational linear relation between positive cube
-- roots of 2 and 4 forces all three rational coefficients to vanish.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module algebra_apbmpcneq0_aeq0anbeq0anceq0 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≈Q_ _≈ℝ_
infixr 4 _∧_

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data NatLe : Nat → Nat → Set where
  zero-le :
    {n : Nat} → NatLe zero n
  successor-le :
    {m n : Nat} → NatLe m n → NatLe (suc m) (suc n)

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} → NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- The fraction p n d represents the rational number (p - n) / (d + 1).
-- Thus every rational has a representative and every stored denominator is
-- positive.
record Rat : Set where
  constructor fraction
  field
    positiveNumerator   : Nat
    negativeNumerator   : Nat
    denominatorMinusOne : Nat

open Rat public

denominator : Rat → Nat
denominator q = suc (denominatorMinusOne q)

zeroQ : Rat
zeroQ = fraction zero zero zero

oneQ : Rat
oneQ = fraction (suc zero) zero zero

fromNatQ : Nat → Rat
fromNatQ n = fraction n zero zero

-- Cross multiplication gives equality of the represented rational values.
_≈Q_ : Rat → Rat → Set
fraction p n d ≈Q fraction q m e =
  (p * suc e) + (m * suc d) ≡
  (q * suc d) + (n * suc e)

ratAdd : Rat → Rat → Rat
ratAdd (fraction p n d) (fraction q m e) =
  fraction
    ((p * suc e) + (q * suc d))
    ((n * suc e) + (m * suc d))
    (pred (suc d * suc e))

ratMultiply : Rat → Rat → Rat
ratMultiply (fraction p n d) (fraction q m e) =
  fraction
    ((p * q) + (n * m))
    ((p * m) + (n * q))
    (pred (suc d * suc e))

RationalLess : Rat → Rat → Set
RationalLess (fraction p n d) (fraction q m e) =
  NatLess
    ((p * suc e) + (m * suc d))
    ((q * suc d) + (n * suc e))

Positive : Rat → Set
Positive epsilon =
  RationalLess zeroQ epsilon

Close : Rat → Rat → Rat → Set
Close x y epsilon =
  RationalLess x (ratAdd y epsilon) ∧
  RationalLess y (ratAdd x epsilon)

Sequence : Set
Sequence = Nat → Rat

Cauchy : Sequence → Set
Cauchy sequence =
  (epsilon : Rat) →
  Positive epsilon →
  Exists Nat λ threshold →
    (m n : Nat) →
    NatLe threshold m →
    NatLe threshold n →
    Close (sequence m) (sequence n) epsilon

-- Rational Cauchy representatives modulo _≈ℝ_ are the standard real
-- completion of the rationals.
record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    isCauchy      : Cauchy approximation

open Real public

EventuallyEquivalent : Sequence → Sequence → Set
EventuallyEquivalent left right =
  (epsilon : Rat) →
  Positive epsilon →
  Exists Nat λ threshold →
    (n : Nat) →
    NatLe threshold n →
    Close (left n) (right n) epsilon

_≈ℝ_ : Sequence → Sequence → Set
_≈ℝ_ = EventuallyEquivalent

constantSequence : Rat → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (fromNatQ n)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd left right n =
  ratAdd (left n) (right n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right n =
  ratMultiply (left n) (right n)

sequencePower : Sequence → Nat → Sequence
sequencePower sequence zero =
  constantSequence oneQ
sequencePower sequence (suc exponent) =
  sequenceMultiply sequence (sequencePower sequence exponent)

-- A positive rational gap eventually below a Cauchy representative is
-- exactly strict positivity of its represented real limit.
PositiveReal : Real → Set
PositiveReal x =
  Exists Rat λ gap →
    Positive gap ∧
    Exists Nat λ threshold →
      (n : Nat) →
      NatLe threshold n →
      RationalLess gap (approximation x n)

linearCombination :
  Rat →
  Rat →
  Rat →
  Real →
  Real →
  Sequence
linearCombination a b c m n =
  sequenceAdd
    (sequenceAdd
      (constantSequence a)
      (sequenceMultiply
        (constantSequence b)
        (approximation m)))
    (sequenceMultiply
      (constantSequence c)
      (approximation n))

-- Pointwise rational arithmetic descends to the Cauchy quotient, so every
-- _≈ℝ_ below is bidirectionally equivalent to the corresponding equality in
-- the fixed standard real field.
algebra_apbmpcneq0_aeq0anbeq0anceq0 : Set
algebra_apbmpcneq0_aeq0anbeq0anceq0 =
  (a b c : Rat) →
  (m n : Real) →
  PositiveReal m ∧ PositiveReal n →
  sequencePower (approximation m) 3 ≈ℝ naturalSequence 2 →
  sequencePower (approximation n) 3 ≈ℝ naturalSequence 4 →
  linearCombination a b c m n ≈ℝ constantSequence zeroQ →
  (a ≈Q zeroQ) ∧ (b ≈Q zeroQ) ∧ (c ≈Q zeroQ)
