-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_b5:
-- for prime p, the number of 2 x 2 matrices over the p-element field with
-- trace 1 and determinant 0 is p squared plus p. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Top : Set where
  constructor truth

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

CarrierHasCardinality :
  Set ->
  Nat ->
  Set
CarrierHasCardinality A cardinality =
  HasCardinality {A = A} (\ _ -> Top) cardinality

record Field (F : Set) : Set1 where
  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    zero-not-one :
      zeroF != oneF

    add-commutative :
      (x y : F) ->
      add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) ->
      add x zeroF == x
    add-inverse :
      (x : F) ->
      add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : F) ->
      multiply x oneF == x
    distribute :
      (x y z : F) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiply x (inverse x) == oneF

open Field

subtract :
  {F : Set} ->
  Field F ->
  F ->
  F ->
  F
subtract fieldStructure x y =
  add fieldStructure x (negate fieldStructure y)

record Matrix2 (F : Set) : Set where
  constructor matrix
  field
    entry00 : F
    entry01 : F
    entry10 : F
    entry11 : F

open Matrix2

Qualifying :
  {F : Set} ->
  Field F ->
  Matrix2 F ->
  Set
Qualifying fieldStructure M =
  add fieldStructure
    (entry00 M)
    (entry11 M)
  == oneF fieldStructure
  and
  subtract fieldStructure
    (multiply fieldStructure
      (entry00 M)
      (entry11 M))
    (multiply fieldStructure
      (entry01 M)
      (entry10 M))
  == zeroF fieldStructure

Divides :
  Nat ->
  Nat ->
  Set
Divides divisor number =
  Exists Nat
    (\ factor -> divisor * factor == number)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Prime :
  Nat ->
  Set
Prime p =
  twoN <=N p
  and
  ((divisor : Nat) ->
    Divides divisor p ->
    divisor == oneN or divisor == p)

putnam-1968-b5 : Set1
putnam-1968-b5 =
  (p : Nat) ->
  Prime p ->
  (F : Set) ->
  (fieldStructure : Field F) ->
  CarrierHasCardinality F p ->
  HasCardinality
    (Qualifying fieldStructure)
    (p * p + p)
