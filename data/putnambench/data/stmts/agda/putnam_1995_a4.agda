-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_a4:
-- a cyclic integer-labeled necklace of positive length and total label sum n - 1
-- has a cut whose every nonempty prefix sum is at most its length minus one.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; mod-helper)

infix 4 _<=N_ _<=Z_
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data _<=Z_ : Int -> Int -> Set where
  negative<=positive :
    {m n : Nat} ->
    negsuc m <=Z pos n
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

sumThrough : (Nat -> Int) -> Nat -> Int
sumThrough term zero =
  term zero
sumThrough term (suc n) =
  addInt (sumThrough term n) (term (suc n))

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

putnam-1995-a4 : Set
putnam-1995-a4 =
  (n : Nat) ->
  Positive n ->
  (necklace : Nat -> Int) ->
  sumThrough necklace (n - 1) == difference n 1 ->
  Exists Nat
    (\ cut ->
      (cut <=N (n - 1))
      and
      ((k : Nat) ->
        k <=N (n - 1) ->
        sumThrough
          (\ i -> necklace (naturalMod (cut + i) n))
          k
        <=Z
        pos k))
