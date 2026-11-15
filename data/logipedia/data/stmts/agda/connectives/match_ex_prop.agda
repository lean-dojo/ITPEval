-- Statement-only formalization of Logipedia corpus artifact
-- connectives.match_ex_prop (catalog title "connectives.match_ex_prop"):
-- the elimination principle for the primitive existential connective ex.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module match_ex_prop where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (ex :
    (A : Set type-level) ->
    (A -> Set proposition-level) ->
    Set proposition-level) where

  match-ex-prop :
    Set (lsuc (type-level ⊔ proposition-level))
  match-ex-prop =
    (A : Set type-level) ->
    (P : A -> Set proposition-level) ->
    (return : Set proposition-level) ->
    ((x : A) -> P x -> return) ->
    ex A P ->
    return
