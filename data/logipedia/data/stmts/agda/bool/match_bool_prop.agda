-- Statement-only formalization of Logipedia corpus artifact
-- bool.match_bool_prop (catalog title "bool.match_bool_prop"): every predicate
-- on the Boolean carrier that holds at true and false holds at every Boolean.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module match_bool_prop where

open import Agda.Primitive using (Level; _⊔_; lsuc)

module Statement
  {bool-level proposition-level : Level}
  (Bool : Set bool-level)
  (true false : Bool) where

  match-bool-prop :
    Set (bool-level ⊔ lsuc proposition-level)
  match-bool-prop =
    (return : Bool → Set proposition-level) →
    return true →
    return false →
    (z : Bool) →
    return z
