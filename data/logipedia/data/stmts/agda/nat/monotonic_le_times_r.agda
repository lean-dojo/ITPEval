-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_le_times_r (catalog title "nat.monotonic_le_times_r"):
-- multiplication by a fixed natural number on the left is monotone in the
-- right factor. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_le_times_r where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

monotonic-le-times-r : Set
monotonic-le-times-r =
  (n x y : Nat) ->
  x <= y ->
  (n * x) <= (n * y)
