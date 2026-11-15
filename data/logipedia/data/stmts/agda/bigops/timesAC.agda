-- Statement-only formalization of Logipedia corpus artifact bigops.timesAC
-- (catalog title "bigops.timesAC"): the source module's opaque ACop predicate
-- holds for the natural number one. This file contains no proof.

{-# OPTIONS --safe #-}

module timesAC where

open import Agda.Builtin.Nat using (Nat; zero; suc)

module Statement
  (ACop : (A : Set) -> A -> Set) where

  times-AC : Set
  times-AC =
    ACop Nat (suc zero)
