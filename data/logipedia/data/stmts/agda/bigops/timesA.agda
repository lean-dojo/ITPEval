-- Statement-only formalization of Logipedia corpus artifact bigops.timesA
-- (catalog title "bigops.timesA"): the source module's opaque Aop predicate
-- holds for the natural number one. This file contains no proof.

{-# OPTIONS --safe #-}

module timesA where

open import Agda.Builtin.Nat using (Nat; zero; suc)

module Statement
  (Aop : (A : Set) -> A -> Set) where

  times-A : Set
  times-A =
    Aop Nat (suc zero)
