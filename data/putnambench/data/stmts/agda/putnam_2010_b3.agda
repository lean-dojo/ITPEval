-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_b3
-- (putnambench__agda__putnam_2010_b3): redistribution among 2010 labeled
-- boxes by moving the source box's label number of balls, classified by
-- exactly the positive integers n at least 1005. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2010B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat :
  {n : Nat} ->
  Fin n ->
  Nat
finToNat fzero =
  zero
finToNat (fsuc index) =
  suc (finToNat index)

sumFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFin {zero} values =
  zero
sumFin {suc n} values =
  values fzero + sumFin (\ index -> values (fsuc index))

Box : Set
Box =
  Fin 2010

Distribution : Set
Distribution =
  Box -> Nat

Process : Set
Process =
  Nat -> Distribution

SameDistribution :
  Distribution ->
  Distribution ->
  Set
SameDistribution left right =
  (box : Box) ->
  left box == right box

Move :
  Process ->
  Nat ->
  Set
Move process time =
  Exists Box
    (\ source ->
      Exists Box
        (\ destination ->
          source != destination
          and
          suc (finToNat source) <=N process time source
          and
          process (suc time) source
            == process time source - suc (finToNat source)
          and
          process (suc time) destination
            == process time destination + suc (finToNat source)
          and
          ((box : Box) ->
            box != source ->
            box != destination ->
            process (suc time) box == process time box)))

ValidThrough :
  Process ->
  Nat ->
  Set
ValidThrough process stoppingTime =
  (time : Nat) ->
  time <N stoppingTime ->
  Move process time

Uniform :
  Nat ->
  Distribution ->
  Set
Uniform n distribution =
  (box : Box) ->
  distribution box == n

CanReachUniform :
  Distribution ->
  Nat ->
  Set
CanReachUniform initial n =
  Exists Process
    (\ process ->
      Exists Nat
        (\ stoppingTime ->
          SameDistribution (process zero) initial
          and
          ValidThrough process stoppingTime
          and
          Uniform n (process stoppingTime)))

putnam-2010-b3 : Set
putnam-2010-b3 =
  (n : Nat) ->
  zero <N n ->
  Iff
    ((initial : Distribution) ->
      sumFin initial == 2010 * n ->
      CanReachUniform initial n)
    (1005 <=N n)
