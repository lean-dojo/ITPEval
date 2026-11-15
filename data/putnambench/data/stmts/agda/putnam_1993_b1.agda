-- Statement-only formalization of PutnamBench corpus artifact putnam_1993_b1
-- (putnambench__agda__putnam_1993_b1): 3987 is the least positive integer n
-- satisfying the stated rational interval condition. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1993B1 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _<N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

one : Nat
one =
  suc zero

bound : Nat
bound =
  1993

next-bound : Nat
next-bound =
  1994

solution : Nat
solution =
  3987

Qualifies : Nat -> Set
Qualifies n =
  zero <N n
  and
  ((m : Nat) ->
    zero <N m ->
    m <N bound ->
    Exists Nat
      (\ k ->
        (m * n <N k * bound)
        and
        (k * next-bound <N (m + one) * n)))

record IsLeastQualifying (least : Nat) : Set where
  field
    qualifies :
      Qualifies least
    least-bound :
      (n : Nat) ->
      Qualifies n ->
      least <=N n

putnam-1993-b1 : Set
putnam-1993-b1 =
  IsLeastQualifying solution
