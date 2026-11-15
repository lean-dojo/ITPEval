-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_b3
-- (putnambench__agda__putnam_2013_b3): additive representation of a real
-- valuation on a finite family of subsets closed under unions and intersections.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

data Top : Set where
  trivial : Top

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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) ->
      lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data FiniteSubset : Nat -> Set where
  emptySubset : FiniteSubset zero
  addBit      : {n : Nat} -> Bool -> FiniteSubset n -> FiniteSubset (suc n)

data IsTrue : Bool -> Set where
  true-witness : IsTrue true

emptyFor : (n : Nat) -> FiniteSubset n
emptyFor zero =
  emptySubset
emptyFor (suc n) =
  addBit false (emptyFor n)

boolAnd : Bool -> Bool -> Bool
boolAnd false second-bit =
  false
boolAnd true second-bit =
  second-bit

boolOr : Bool -> Bool -> Bool
boolOr false second-bit =
  second-bit
boolOr true second-bit =
  true

intersection :
  {n : Nat} ->
  FiniteSubset n ->
  FiniteSubset n ->
  FiniteSubset n
intersection emptySubset emptySubset =
  emptySubset
intersection (addBit left-bit left-tail) (addBit right-bit right-tail) =
  addBit
    (boolAnd left-bit right-bit)
    (intersection left-tail right-tail)

union :
  {n : Nat} ->
  FiniteSubset n ->
  FiniteSubset n ->
  FiniteSubset n
union emptySubset emptySubset =
  emptySubset
union (addBit left-bit left-tail) (addBit right-bit right-tail) =
  addBit
    (boolOr left-bit right-bit)
    (union left-tail right-tail)

data BitIncluded : Bool -> Bool -> Set where
  false-included-false : BitIncluded false false
  false-included-true  : BitIncluded false true
  true-included-true   : BitIncluded true true

Subset :
  {n : Nat} ->
  FiniteSubset n ->
  FiniteSubset n ->
  Set
Subset emptySubset emptySubset =
  Top
Subset (addBit left-bit left-tail) (addBit right-bit right-tail) =
  BitIncluded left-bit right-bit and Subset left-tail right-tail

ProperSubset :
  {n : Nat} ->
  FiniteSubset n ->
  FiniteSubset n ->
  Set
ProperSubset smaller larger =
  Subset smaller larger and smaller != larger

boolCardinality : Bool -> Nat
boolCardinality false =
  zero
boolCardinality true =
  suc zero

cardinality :
  {n : Nat} ->
  FiniteSubset n ->
  Nat
cardinality emptySubset =
  zero
cardinality (addBit bit tail) =
  boolCardinality bit + cardinality tail

weightedSum :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> R) ->
  FiniteSubset n ->
  R
weightedSum reals weights emptySubset =
  zeroR reals
weightedSum reals weights (addBit false tail) =
  weightedSum reals (\ index -> weights (fsuc index)) tail
weightedSum reals weights (addBit true tail) =
  add reals
    (weights fzero)
    (weightedSum reals (\ index -> weights (fsuc index)) tail)

NonemptyFamily :
  {n : Nat} ->
  (FiniteSubset n -> Bool) ->
  Set
NonemptyFamily P =
  Exists _ (\ subset -> IsTrue (P subset))

ClosedUnderUnionAndIntersection :
  {n : Nat} ->
  (FiniteSubset n -> Bool) ->
  Set
ClosedUnderUnionAndIntersection P =
  (first-subset second-subset : FiniteSubset _) ->
  IsTrue (P first-subset) ->
  IsTrue (P second-subset) ->
  IsTrue (P (union first-subset second-subset))
  and
  IsTrue (P (intersection first-subset second-subset))

HasOneElementPredecessors :
  {n : Nat} ->
  (FiniteSubset n -> Bool) ->
  Set
HasOneElementPredecessors {n} P =
  (subset : FiniteSubset _) ->
  IsTrue (P subset) ->
  subset != emptyFor n ->
  Exists _
    (\ predecessor ->
      IsTrue (P predecessor)
      and
      ProperSubset predecessor subset
      and
      cardinality predecessor + suc zero == cardinality subset)

ValuationIdentity :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (FiniteSubset n -> Bool) ->
  (FiniteSubset n -> R) ->
  Set
ValuationIdentity reals P function =
  (first-subset second-subset : FiniteSubset _) ->
  IsTrue (P first-subset) ->
  IsTrue (P second-subset) ->
  function (union first-subset second-subset) ==
  subtract reals
    (add reals (function first-subset) (function second-subset))
    (function (intersection first-subset second-subset))

HasElementWeightRepresentation :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (FiniteSubset n -> Bool) ->
  (FiniteSubset n -> R) ->
  Set
HasElementWeightRepresentation reals P function =
  Exists _
    (\ weights ->
      (subset : FiniteSubset _) ->
      IsTrue (P subset) ->
      function subset == weightedSum reals weights subset)

putnam-2013-b3 : Set1
putnam-2013-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  (P : FiniteSubset n -> Bool) ->
  (function : FiniteSubset n -> R) ->
  NonemptyFamily P ->
  ClosedUnderUnionAndIntersection P ->
  HasOneElementPredecessors P ->
  function (emptyFor n) == zeroR reals ->
  ValuationIdentity reals P function ->
  HasElementWeightRepresentation reals P function
