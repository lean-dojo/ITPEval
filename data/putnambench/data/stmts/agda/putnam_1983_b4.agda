-- Statement-only formalization of PutnamBench corpus artifact putnam_1983_b4:
-- every positive natural sequence obtained by adding the floor of the square
-- root of each term eventually contains a perfect square. This file contains
-- no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _<_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

one : Nat
one =
  suc zero

FloorSquareRoot : Nat -> Nat -> Set
FloorSquareRoot n r =
  (r * r <= n)
  and
  (n < suc r * suc r)

SatisfiesRecurrence : (Nat -> Nat) -> Set
SatisfiesRecurrence a =
  (n : Nat) ->
  Exists Nat
    (\ r ->
      FloorSquareRoot (a n) r
      and
      a (suc n) == a n + r)

putnam-1983-b4 : Set
putnam-1983-b4 =
  (a : Nat -> Nat) ->
  one <= a zero ->
  SatisfiesRecurrence a ->
  Exists Nat
    (\ i ->
      Exists Nat
        (\ s ->
          a i == s * s))
