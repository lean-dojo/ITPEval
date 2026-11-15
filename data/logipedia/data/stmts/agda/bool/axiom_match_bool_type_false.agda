-- Statement-only formalization of Logipedia corpus artifact
-- bool.axiom_match_bool_type_false (catalog title
-- "bool.axiom_match_bool_type_false"): matching the Boolean false value
-- selects the false branch for every result type. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_match_bool_type_false where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {bool-level return-level : Level}
  (Bool : Set bool-level)
  (false : Bool)
  (equal : (A : Set return-level) -> A -> A -> Set return-level)
  (match-bool-type :
    (A : Set return-level) -> A -> A -> Bool -> A) where

  axiom-match-bool-type-false :
    Set (lsuc return-level)
  axiom-match-bool-type-false =
    (return : Set return-level) ->
    (case-true case-false : return) ->
    equal
      return
      (match-bool-type return case-true case-false false)
      case-false
