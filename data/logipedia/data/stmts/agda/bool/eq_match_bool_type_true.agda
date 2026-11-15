-- Statement-only formalization of Logipedia corpus artifact
-- bool.eq_match_bool_type_true (catalog title
-- "bool.eq_match_bool_type_true"): Leibniz equality states that matching the
-- Boolean true value selects the true branch for every result type.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module eq_match_bool_type_true where

open import Agda.Primitive using (Level; lsuc)

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

module Statement
  {bool-level return-level : Level}
  (Bool : Set bool-level)
  (true : Bool)
  (match-bool-type :
    (A : Set return-level) -> A -> A -> Bool -> A) where

  eq-match-bool-type-true :
    Set (lsuc return-level)
  eq-match-bool-type-true =
    (return : Set return-level) ->
    (case-true case-false : return) ->
    Leibniz
      return
      (match-bool-type return case-true case-false true)
      case-true
