-- Statement-only formalization of Logipedia corpus artifact
-- bool.sym_eq_match_bool_type_true (catalog title
-- "bool.sym_eq_match_bool_type_true"): Leibniz equality states that the true
-- branch equals the result of matching the Boolean true value for every
-- result type. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_match_bool_type_true where

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

  sym-eq-match-bool-type-true :
    Set (lsuc return-level)
  sym-eq-match-bool-type-true =
    (return : Set return-level) ->
    (case-true case-false : return) ->
    Leibniz
      return
      case-true
      (match-bool-type return case-true case-false true)
