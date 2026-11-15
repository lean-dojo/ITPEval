-- Statement-only formalization of Logipedia corpus artifact
-- bool.axiom_match_bool_type_true (catalog title
-- "bool.axiom_match_bool_type_true"): matching the Boolean true value
-- selects the true branch for every result type. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_match_bool_type_true where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {bool-level return-level : Level}
  (Bool : Set bool-level)
  (true : Bool)
  (equal : (A : Set return-level) -> A -> A -> Set return-level)
  (match-bool-type :
    (A : Set return-level) -> A -> A -> Bool -> A) where

  axiom-match-bool-type-true :
    Set (lsuc return-level)
  axiom-match-bool-type-true =
    (return : Set return-level) ->
    (case-true case-false : return) ->
    equal
      return
      (match-bool-type return case-true case-false true)
      case-true
