-- Statement-only formalization of Logipedia corpus artifact
-- bool.true_or_false (catalog title "bool.true_or_false"): every Boolean is
-- equal to true or equal to false. This file contains no proof.

{-# OPTIONS --safe #-}

module true_or_false where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

infixr 2 _∨_

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

true-or-false : Set
true-or-false =
  (b : Bool) →
  (b ≡ true) ∨ (b ≡ false)
