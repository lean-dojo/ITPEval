-- Statement-only formalization of Logipedia corpus artifact connectives.or_introl
-- (catalog title "connectives.or_introl"): the introduction principle for the
-- primitive disjunction connective Or. This file contains no proof.

{-# OPTIONS --safe #-}

module or_introl where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (Or : Set proposition-level -> Set proposition-level -> Set proposition-level)
  where

  connectives-or-introl : Set (lsuc proposition-level)
  connectives-or-introl =
    (A B : Set proposition-level) ->
    A ->
    Or A B
