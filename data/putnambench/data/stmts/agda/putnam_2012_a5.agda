-- Statement-only formalization of PutnamBench corpus artifact putnam_2012_a5
-- (putnambench__agda__putnam_2012_a5): classification of the prime field
-- dimensions admitting an affine linear map whose first p^n iterates of zero
-- are pairwise distinct. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2012A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

power : Nat -> Nat -> Nat
power base zero =
  oneN
power base (suc exponent) =
  base * power base exponent

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ factor ->
      divisor * factor == number)

Prime : Nat -> Set
Prime p =
  twoN <=N p
  and
  ((divisor : Nat) ->
    Divides divisor p ->
    divisor == oneN or divisor == p)

Positive : Nat -> Set
Positive n =
  oneN <=N n

record Field (F : Set) : Set where
  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    one-not-zero :
      oneF != zeroF

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

record HasCardinality (A : Set) (cardinality : Nat) : Set where
  field
    enumerate :
      Fin cardinality ->
      A
    index :
      A ->
      Fin cardinality
    enumerate-index :
      (x : A) ->
      enumerate (index x) == x
    index-enumerate :
      (i : Fin cardinality) ->
      index (enumerate i) == i

Vector : Set -> Nat -> Set
Vector F n =
  Fin n -> F

Matrix : Set -> Nat -> Set
Matrix F n =
  Fin n -> Fin n -> F

sumFin :
  {F : Set} ->
  Field F ->
  {n : Nat} ->
  (Fin n -> F) ->
  F
sumFin fieldStructure {zero} term =
  zeroF fieldStructure
sumFin fieldStructure {suc n} term =
  add fieldStructure
    (term fzero)
    (sumFin fieldStructure (\ i -> term (fsuc i)))

zeroVector :
  {F : Set} ->
  Field F ->
  {n : Nat} ->
  Vector F n
zeroVector fieldStructure i =
  zeroF fieldStructure

matrixVectorProduct :
  {F : Set} ->
  Field F ->
  {n : Nat} ->
  Matrix F n ->
  Vector F n ->
  Vector F n
matrixVectorProduct fieldStructure M x i =
  sumFin fieldStructure
    (\ j ->
      multiply fieldStructure (M i j) (x j))

affine :
  {F : Set} ->
  Field F ->
  {n : Nat} ->
  Matrix F n ->
  Vector F n ->
  Vector F n ->
  Vector F n
affine fieldStructure M v x i =
  add fieldStructure
    (v i)
    (matrixVectorProduct fieldStructure M x i)

iterate :
  {A : Set} ->
  Nat ->
  (A -> A) ->
  A ->
  A
iterate zero function x =
  x
iterate (suc count) function x =
  function (iterate count function x)

VectorEqual :
  {F : Set} ->
  {n : Nat} ->
  Vector F n ->
  Vector F n ->
  Set
VectorEqual {n = n} x y =
  (coordinate : Fin n) ->
  x coordinate == y coordinate

OrbitValue :
  {F : Set} ->
  Field F ->
  {n p : Nat} ->
  Matrix F n ->
  Vector F n ->
  Fin (power p n) ->
  Vector F n
OrbitValue fieldStructure M v step =
  iterate
    (suc (finToNat step))
    (affine fieldStructure M v)
    (zeroVector fieldStructure)

FullDistinctOrbit :
  {F : Set} ->
  Field F ->
  {n p : Nat} ->
  Matrix F n ->
  Vector F n ->
  Set
FullDistinctOrbit fieldStructure {n} {p} M v =
  Not
    (Exists (Fin (power p n))
      (\ i ->
        Exists (Fin (power p n))
          (\ j ->
            i != j
            and
            VectorEqual
              (OrbitValue fieldStructure M v i)
              (OrbitValue fieldStructure M v j))))

AdmissibleDimensions : Nat -> Nat -> Set
AdmissibleDimensions n p =
  n == oneN
  or
  (n == twoN and p == twoN)

putnam-2012-a5 : Set1
putnam-2012-a5 =
  (n p : Nat) ->
  Positive n ->
  Prime p ->
  (F : Set) ->
  (fieldStructure : Field F) ->
  HasCardinality F p ->
  AdmissibleDimensions n p
  iff
  Exists (Matrix F n)
    (\ M ->
      Exists (Vector F n)
        (\ v ->
          FullDistinctOrbit
            fieldStructure
            {n = n}
            {p = p}
            M
            v))
