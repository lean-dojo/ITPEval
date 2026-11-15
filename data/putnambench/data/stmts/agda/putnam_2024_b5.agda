-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_b5
-- (putnambench__agda__putnam_2024_b5): the number of pairs of nondecreasing
-- positive integer sequences with a common bounded upper endpoint is a
-- polynomial in the bound with nonnegative rational coefficients. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2024B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
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

Positive : Nat -> Set
Positive n =
  suc zero <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

last : {n : Nat} -> Fin (suc n)
last {zero} =
  fzero
last {suc n} =
  fsuc last

MonotoneNatSequence :
  {q : Nat} ->
  (Fin q -> Nat) ->
  Set
MonotoneNatSequence {q} sequence =
  (i j : Fin q) ->
  toNat i <=N toNat j ->
  sequence i <=N sequence j

QualifyingSequence :
  {q : Nat} ->
  (Fin (suc q) -> Nat) ->
  Nat ->
  Set
QualifyingSequence sequence upper =
  MonotoneNatSequence sequence
  and
  (suc zero <=N sequence fzero
  and
  sequence last <=N upper)

record SequenceTriple (k m : Nat) : Set where
  constructor triple
  field
    x-sequence : Fin k -> Nat
    y-sequence : Fin m -> Nat
    endpoint   : Nat

open SequenceTriple

SameSequenceTriple :
  {k m : Nat} ->
  SequenceTriple k m ->
  SequenceTriple k m ->
  Set
SameSequenceTriple {k} {m} left-triple right-triple =
  ((i : Fin k) ->
    x-sequence left-triple i ==
    x-sequence right-triple i)
  and
  (((j : Fin m) ->
    y-sequence left-triple j ==
    y-sequence right-triple j)
  and
  endpoint left-triple == endpoint right-triple)

QualifyingTriple :
  (k-minus-one m-minus-one n : Nat) ->
  SequenceTriple (suc k-minus-one) (suc m-minus-one) ->
  Set
QualifyingTriple k-minus-one m-minus-one n sequences =
  QualifyingSequence
    (x-sequence sequences)
    (endpoint sequences)
  and
  (QualifyingSequence
    (y-sequence sequences)
    (endpoint sequences)
  and
  endpoint sequences <=N n)

record HasExtensionalCardinality
  {A : Set}
  (member : A -> Set)
  (equivalent : A -> A -> Set)
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
        (\ index ->
          equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

CountsQualifyingTriples :
  Nat ->
  Nat ->
  (Nat -> Nat) ->
  Set
CountsQualifyingTriples k-minus-one m-minus-one f =
  (n : Nat) ->
  HasExtensionalCardinality
    (QualifyingTriple k-minus-one m-minus-one n)
    SameSequenceTriple
    (f n)

record RationalField (Q : Set) : Set1 where
  field
    zeroQ oneQ : Q
    add multiply : Q -> Q -> Q
    negate inverse : Q -> Q
    lessOrEqual : Q -> Q -> Set
    fromNat : Nat -> Q
    fromInt : Int -> Q

    one-not-zero :
      oneQ != zeroQ

    add-commutative :
      (x y : Q) -> add x y == add y x
    add-associative :
      (x y z : Q) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : Q) -> add x zeroQ == x
    add-inverse :
      (x : Q) -> add x (negate x) == zeroQ

    multiply-commutative :
      (x y : Q) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : Q) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : Q) -> multiply x oneQ == x
    multiply-zero :
      (x : Q) -> multiply x zeroQ == zeroQ
    distribute :
      (x y z : Q) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroQ == zeroQ
    multiply-inverse :
      (x : Q) ->
      x != zeroQ ->
      multiply x (inverse x) == oneQ

    order-reflexive :
      (x : Q) -> lessOrEqual x x
    order-transitive :
      (x y z : Q) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : Q) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : Q) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : Q) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : Q) ->
      lessOrEqual zeroQ x ->
      lessOrEqual zeroQ y ->
      lessOrEqual zeroQ (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroQ oneQ and zeroQ != oneQ

    fromNat-zero :
      fromNat zero == zeroQ
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneQ
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    fromInt-nonnegative :
      (n : Nat) ->
      fromInt (pos n) == fromNat n
    fromInt-negative :
      (n : Nat) ->
      fromInt (negsuc n) == negate (fromNat (suc n))

    every-element-is-ratio :
      (x : Q) ->
      Exists Int
        (\ numerator ->
          Exists Nat
            (\ denominator-minus-one ->
              x ==
              multiply
                (fromInt numerator)
                (inverse
                  (fromNat (suc denominator-minus-one)))))

open RationalField

coefficient :
  {Q : Set} ->
  RationalField Q ->
  List Q ->
  Nat ->
  Q
coefficient rationals [] index =
  zeroQ rationals
coefficient rationals (value ∷ values) zero =
  value
coefficient rationals (value ∷ values) (suc index) =
  coefficient rationals values index

evaluatePolynomial :
  {Q : Set} ->
  RationalField Q ->
  List Q ->
  Q ->
  Q
evaluatePolynomial rationals [] x =
  zeroQ rationals
evaluatePolynomial rationals (value ∷ values) x =
  add rationals
    value
    (multiply rationals
      x
      (evaluatePolynomial rationals values x))

AllCoefficientsNonnegative :
  {Q : Set} ->
  RationalField Q ->
  List Q ->
  Set
AllCoefficientsNonnegative rationals values =
  (index : Nat) ->
  lessOrEqual rationals
    (zeroQ rationals)
    (coefficient rationals values index)

putnam-2024-b5 : Set1
putnam-2024-b5 =
  (Q : Set) ->
  (rationals : RationalField Q) ->
  (k-minus-one m-minus-one : Nat) ->
  (f : Nat -> Nat) ->
  CountsQualifyingTriples k-minus-one m-minus-one f ->
  Exists (List Q)
    (\ coefficients ->
      ((n : Nat) ->
        Positive n ->
        fromNat rationals (f n) ==
        evaluatePolynomial rationals
          coefficients
          (fromNat rationals n))
      and
      AllCoefficientsNonnegative rationals coefficients)
