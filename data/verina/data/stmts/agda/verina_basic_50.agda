-- Statement-only formalization of VERINA corpus artifact verina_basic_50,
-- catalog title "Abs": a deterministic integer absolute-value program returns
-- the input when nonnegative and its additive inverse when negative, connected
-- to its precondition/postcondition correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic50 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data Nonnegative : Int → Set where
  nonnegative : {n : Nat} → Nonnegative (pos n)

data Negative : Int → Set where
  negative : {n : Nat} → Negative (negsuc n)

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

zeroInt : Int
zeroInt = pos zero

Abs-precond : Int → Set
Abs-precond x = Top

Abs :
  (x : Int) →
  Abs-precond x →
  Int
Abs (pos n) h-precond = pos n
Abs (negsuc n) h-precond = pos (suc n)

Abs-postcond :
  (x : Int) →
  (result : Int) →
  Abs-precond x →
  Set
Abs-postcond x result h-precond =
  (Nonnegative x → x ≡ result) ∧
  (Negative x → intAdd x result ≡ zeroInt)

Abs-spec-satisfied : Set
Abs-spec-satisfied =
  (x : Int) →
  (h-precond : Abs-precond x) →
  Abs-postcond
    x
    (Abs x h-precond)
    h-precond
