-- Statement-only formalization of miniF2F valid problem mathd_algebra_69. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module mathd-algebra-69 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; _*_)

mathd-algebra-69 : Set
mathd-algebra-69 =
  (rows seats : Nat) →
  rows * seats ≡ 450 →
  (rows + 5) * (seats - 3) ≡ 450 →
  rows ≡ 25
