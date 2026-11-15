-- Statement-only formalization of Logipedia corpus artifact
-- bool.not_eq_true_false (catalog title "bool.not_eq_true_false"): Boolean
-- true is not equal to Boolean false. This file contains no proof.

{-# OPTIONS --safe #-}

module not_eq_true_false where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

data Bottom : Set where

Not : Set → Set
Not proposition =
  proposition → Bottom

not-eq-true-false : Set
not-eq-true-false =
  Not (true ≡ false)
