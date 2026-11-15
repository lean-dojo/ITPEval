-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_a2:
-- in the concatenation of the positive integers, the digit at position
-- 10^1987 lies in the block of 1984-digit integers. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1987A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _<N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

ten : Nat
ten =
  10

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

record DecimalDigitCount (n digits : Nat) : Set where
  constructor decimal-digit-count
  field
    exponent   : Nat
    count      : digits == suc exponent
    lower-bound : power ten exponent <=N n
    upper-bound : n <N power ten (suc exponent)

putnam-1987-a2 : Set
putnam-1987-a2 =
  (seqind seqsize f numdigits : Nat -> Nat) ->
  (seqind one == one
   and
   ((i : Nat) ->
     two <=N i ->
     seqind i == seqind (i - one) + numdigits (i - one))) ->
  ((i : Nat) ->
    one <=N i ->
    (j : Nat) ->
    j <N numdigits i ->
    seqsize (seqind i + j) == numdigits i) ->
  ((n : Nat) ->
    f n == seqsize (power ten n)) ->
  ((n : Nat) ->
    one <=N n ->
    DecimalDigitCount n (numdigits n)) ->
  f 1987 == 1984
