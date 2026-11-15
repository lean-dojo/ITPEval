-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_b3
-- (putnambench__agda__putnam_1996_b3): the largest cyclic adjacent-product
-- sum over permutations of 1 through n has the stated cubic value. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper; mod-helper)

infix 4 _<=N_
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sumFinNat :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFinNat {zero} terms =
  zero
sumFinNat {suc n} terms =
  terms fzero + sumFinNat (\ i -> terms (fsuc i))

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

sixN : Nat
sixN =
  6

InOneThrough :
  Nat ->
  Nat ->
  Set
InOneThrough n value =
  oneN <=N value
  and
  value <=N n

PermutationOfOneThrough :
  Nat ->
  (Nat -> Nat) ->
  Set
PermutationOfOneThrough n x =
  ((i : Fin n) ->
    InOneThrough n (x (finToNat i)))
  and
  ((value : Nat) ->
    InOneThrough n value ->
    Exists (Fin n)
      (\ i -> x (finToNat i) == value))

CyclicAdjacentProductSum :
  Nat ->
  (Nat -> Nat) ->
  Nat
CyclicAdjacentProductSum n x =
  sumFinNat {n}
    (\ i ->
      x (finToNat i)
      *
      x (naturalMod (suc (finToNat i)) n))

putnam-1996-b3-solution :
  Nat ->
  Nat
putnam-1996-b3-solution n =
  naturalDiv
    (((2 * n * n * n) + (3 * n * n) + 18) - (11 * n))
    sixN

record IsGreatestCyclicSum
  (n maximum : Nat) :
  Set where

  field
    attained :
      Exists (Nat -> Nat)
        (\ x ->
          PermutationOfOneThrough n x
          and
          CyclicAdjacentProductSum n x == maximum)

    upper-bound :
      (x : Nat -> Nat) ->
      PermutationOfOneThrough n x ->
      CyclicAdjacentProductSum n x <=N maximum

putnam-1996-b3 : Set
putnam-1996-b3 =
  (n : Nat) ->
  twoN <=N n ->
  IsGreatestCyclicSum n (putnam-1996-b3-solution n)
