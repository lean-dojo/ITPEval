-- Statement-only formalization of VERINA corpus artifact verina_basic_26,
-- catalog title "isEven": a total integer program returns true exactly when
-- its input has zero remainder modulo two, with the executable implementation
-- connected to its two-direction correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic26 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

naturalModTwo : Nat → Nat
naturalModTwo zero = zero
naturalModTwo (suc zero) = suc zero
naturalModTwo (suc (suc n)) = naturalModTwo n

-- Lean remainder modulo positive two is the nonnegative parity remainder.
moduloByTwo : Int → Int
moduloByTwo (pos n) = pos (naturalModTwo n)
moduloByTwo (negsuc n) = pos (naturalModTwo (suc n))

zeroInt : Int
zeroInt = pos zero

isEven-precond : Int → Set
isEven-precond n = Top

isEven :
  (n : Int) →
  isEven-precond n →
  Bool
isEven n h-precond =
  intEqual (moduloByTwo n) zeroInt

isEven-postcond :
  (n : Int) →
  (result : Bool) →
  isEven-precond n →
  Set
isEven-postcond n result h-precond =
  (IsTrue result → moduloByTwo n ≡ zeroInt) ∧
  (Not (IsTrue result) → Not (moduloByTwo n ≡ zeroInt))

isEven-spec-satisfied : Set
isEven-spec-satisfied =
  (n : Int) →
  (h-precond : isEven-precond n) →
  isEven-postcond
    n
    (isEven n h-precond)
    h-precond
