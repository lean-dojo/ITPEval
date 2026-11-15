-- Statement-only formalization of Logipedia corpus artifact connectives.or_intror
-- (catalog title "connectives.or_intror"): the right introduction principle for
-- the primitive disjunction connective Or. This file contains no proof.

{-# OPTIONS --safe #-}

module or_intror where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (Or : Set proposition-level -> Set proposition-level -> Set proposition-level)
  where

  connectives-or-intror : Set (lsuc proposition-level)
  connectives-or-intror =
    (A B : Set proposition-level) ->
    B ->
    Or A B
