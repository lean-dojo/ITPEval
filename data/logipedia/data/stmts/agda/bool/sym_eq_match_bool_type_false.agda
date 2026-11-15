-- Statement-only formalization of Logipedia corpus artifact
-- bool.sym_eq_match_bool_type_false (catalog title
-- "bool.sym_eq_match_bool_type_false"): Leibniz equality states that the
-- false branch equals the result of matching the Boolean false value for
-- every result type. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_match_bool_type_false where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)

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

match-bool-type :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Bool ->
  A
match-bool-type A case-true case-false true =
  case-true
match-bool-type A case-true case-false false =
  case-false

sym-eq-match-bool-type-false :
  {return-level : Level} ->
  Set (lsuc return-level)
sym-eq-match-bool-type-false {return-level} =
  (return : Set return-level) ->
  (case-true case-false : return) ->
  Leibniz
    return
    case-false
    (match-bool-type return case-true case-false false)
