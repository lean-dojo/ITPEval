-- Statement-only formalization of Logipedia corpus artifact
-- connectives.ex_intro (catalog title "connectives.ex_intro"): the introduction
-- principle for the primitive existential connective ex. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module ex_intro where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (ex :
    (A : Set type-level) ->
    (A -> Set proposition-level) ->
    Set proposition-level) where

  connectives-ex-intro :
    Set (lsuc (type-level ⊔ proposition-level))
  connectives-ex-intro =
    (A : Set type-level) ->
    (P : A -> Set proposition-level) ->
    (x : A) ->
    P x ->
    ex A P
