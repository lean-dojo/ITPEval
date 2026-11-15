-- Statement-only formalization of Logipedia corpus artifact
-- bool.eq_match_bool_type_false (catalog title
-- "bool.eq_match_bool_type_false"): Leibniz equality states that matching the
-- Boolean false value selects the false branch for every result type.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module eq_match_bool_type_false where

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
  (false : Bool)
  (match-bool-type :
    (A : Set return-level) -> A -> A -> Bool -> A) where

  eq-match-bool-type-false :
    Set (lsuc return-level)
  eq-match-bool-type-false =
    (return : Set return-level) ->
    (case-true case-false : return) ->
    Leibniz
      return
      (match-bool-type return case-true case-false false)
      case-false
