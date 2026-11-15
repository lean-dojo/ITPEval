-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_a5
-- (putnambench__agda__putnam_1992_a5): the binary-one parity sequence has no
-- three consecutive equal blocks whose common positive length is also the
-- offset between their starting positions. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

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
  positive : (n : Nat) -> Positive (suc n)

data Bit : Set where
  zeroBit oneBit : Bit

toggle : Bit -> Bit
toggle zeroBit =
  oneBit
toggle oneBit =
  zeroBit

double : Nat -> Nat
double n =
  n + n

record IsBinaryOneParitySequence (a : Nat -> Bit) : Set where
  field
    value-at-zero :
      a zero == zeroBit

    value-at-even-index :
      (n : Nat) ->
      a (double n) == a n

    value-at-odd-index :
      (n : Nat) ->
      a (suc (double n)) == toggle (a n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

ThreeEqualBlocks :
  (Nat -> Bit) ->
  Nat ->
  Nat ->
  Set
ThreeEqualBlocks a k m =
  (j : Nat) ->
  j <=N (m - one) ->
  a (k + j) == a (k + m + j)
  and
  a (k + m + j) == a (k + two * m + j)

HasThreeEqualBlocks :
  (Nat -> Bit) ->
  Set
HasThreeEqualBlocks a =
  Exists Nat
    (\ k ->
      Positive k
      and
      Exists Nat
        (\ m ->
          Positive m
          and
          ThreeEqualBlocks a k m))

putnam-1992-a5 : Set
putnam-1992-a5 =
  (a : Nat -> Bit) ->
  IsBinaryOneParitySequence a ->
  Not (HasThreeEqualBlocks a)
