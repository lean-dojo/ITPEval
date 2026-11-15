-- Statement-only formalization of Logipedia corpus artifact logic.eq_coerc
-- (catalog title "logic.eq_coerc"): equality of propositions permits an
-- inhabitant of the first proposition to inhabit the second. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_coerc where

open import Agda.Builtin.Equality using (_≡_)

eq-coerc : Set₁
eq-coerc =
  (A B : Set) →
  A →
  A ≡ B →
  B
