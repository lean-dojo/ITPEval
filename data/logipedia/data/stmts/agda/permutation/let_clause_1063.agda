-- Statement-only formalization of Logipedia corpus artifact
-- permutation.let_clause_1063 (catalog title "permutation.let_clause_1063"):
-- equality of two bounded inputs transfers the specified image of the second
-- input to the first under the source bounded-permutation context. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module let-clause-1063 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data And (A B : Set) : Set where
  conj : A -> B -> And A B

Injn : (Nat -> Nat) -> Nat -> Set
Injn f n =
  (i j : Nat) ->
  i <= n ->
  j <= n ->
  f i == f j ->
  i == j

Permut : (Nat -> Nat) -> Nat -> Set
Permut f n =
  And
    ((i : Nat) -> i <= n -> f i <= n)
    (Injn f n)

let-clause-1063 : Set
let-clause-1063 =
  (f : Nat -> Nat) ->
  (n : Nat) ->
  Permut f n ->
  (i j : Nat) ->
  i <= n ->
  j <= n ->
  (a : Nat) ->
  And (a <= n) (f a == i) ->
  a <= n ->
  f a == i ->
  (b : Nat) ->
  And (b <= n) (f b == j) ->
  b <= n ->
  f b == j ->
  ((i0 : Nat) -> i0 <= n -> f i0 <= n) ->
  Injn f n ->
  a == b ->
  f a == j
