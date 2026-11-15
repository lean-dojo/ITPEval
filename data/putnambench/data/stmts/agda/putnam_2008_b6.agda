-- Statement-only formalization of PutnamBench corpus artifact putnam_2008_b6:
-- the number of permutations of Fin n moving every index by at most k is odd
-- exactly when n is congruent to 0 or 1 modulo 2k+1. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2008B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _<=N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record _iff_ (A B : Set) : Set where
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

PointwiseEqual :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  (Fin n -> Fin n) ->
  Set
PointwiseEqual {n} left-function right-function =
  (index : Fin n) ->
  left-function index == right-function index

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A} function =
  (x y : A) ->
  function x == function y ->
  x == y

Surjective :
  {A B : Set} ->
  (A -> B) ->
  Set
Surjective {A} {B} function =
  (y : B) ->
  Exists A
    (\ x -> function x == y)

IsPermutation :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  Set
IsPermutation permutation =
  Injective permutation
  and
  Surjective permutation

absoluteDifference : Nat -> Nat -> Nat
absoluteDifference x y =
  (x - y) + (y - x)

KLimited :
  {n : Nat} ->
  Nat ->
  (Fin n -> Fin n) ->
  Set
KLimited {n} k permutation =
  (index : Fin n) ->
  absoluteDifference
    (toNat (permutation index))
    (toNat index)
  <=N
  k

KLimitedPermutation :
  {n : Nat} ->
  Nat ->
  (Fin n -> Fin n) ->
  Set
KLimitedPermutation k permutation =
  IsPermutation permutation
  and
  KLimited k permutation

record HasCardinalityUpTo
  {A : Set}
  (_~_ : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item ~ enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index ~ enumerate right-index ->
      left-index == right-index

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

record Odd (n : Nat) : Set where
  field
    half : Nat
    odd-equation : n == two * half + one

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus left-value right-value =
  naturalMod left-value modulus == naturalMod right-value modulus

putnam-2008-b6 : Set
putnam-2008-b6 =
  (n k : Nat) ->
  Positive n ->
  Positive k ->
  Exists Nat
    (\ count ->
      HasCardinalityUpTo
        {A = Fin n -> Fin n}
        PointwiseEqual
        (KLimitedPermutation k)
        count
      and
      (Odd count
        iff
        (ModEq (two * k + one) n zero
          or
          ModEq (two * k + one) n one)))
