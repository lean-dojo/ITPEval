-- Statement-only formalization of VERINA corpus artifact verina_basic_53,
-- catalog title "CalSum": a deterministic natural-number recursion computes
-- the sum from N down to one and is connected to its arithmetic-series
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic53 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

record Top : Set where
  constructor top

CalSum-precond : Nat → Set
CalSum-precond N = Top

CalSum-loop : Nat → Nat
CalSum-loop zero = zero
CalSum-loop (suc n) =
  suc n + CalSum-loop n

CalSum :
  (N : Nat) →
  CalSum-precond N →
  Nat
CalSum N h-precond =
  CalSum-loop N

CalSum-postcond :
  (N result : Nat) →
  CalSum-precond N →
  Set
CalSum-postcond N result h-precond =
  2 * result ≡ N * (N + 1)

CalSum-spec-satisfied : Set
CalSum-spec-satisfied =
  (N : Nat) →
  (h-precond : CalSum-precond N) →
  CalSum-postcond
    N
    (CalSum N h-precond)
    h-precond
