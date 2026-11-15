-- Statement-only formalization of VERINA corpus artifact verina_basic_66,
-- catalog title "ComputeIsEven": a deterministic integer program tests for
-- zero remainder modulo two and is connected to the contract that it returns
-- true exactly for integers equal to twice another integer. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic66 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _↔_
infixl 7 _*z_

record Top : Set where
  constructor top

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

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

ComputeIsEven-precond : Int → Set
ComputeIsEven-precond x = Top

ComputeIsEven :
  (x : Int) →
  ComputeIsEven-precond x →
  Bool
ComputeIsEven x h-precond =
  if intEqual (moduloByTwo x) zeroInt
  then true
  else false

ComputeIsEven-postcond :
  (x : Int) →
  (result : Bool) →
  ComputeIsEven-precond x →
  Set
ComputeIsEven-postcond x result h-precond =
  (result ≡ true) ↔
  Σ Int (λ k → x ≡ pos 2 *z k)

ComputeIsEven-spec-satisfied : Set
ComputeIsEven-spec-satisfied =
  (x : Int) →
  (h-precond : ComputeIsEven-precond x) →
  ComputeIsEven-postcond
    x
    (ComputeIsEven x h-precond)
    h-precond
