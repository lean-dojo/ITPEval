-- Statement-only formalization of PutnamBench corpus artifact putnam_1971_b3:
-- for every positive start delay T, the set of times t at least T for which
-- floor(t) is twice floor(t - T) has Lebesgue measure one. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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

Predicate : Set -> Set1
Predicate A =
  A -> Set

emptySet :
  {A : Set} ->
  Predicate A
emptySet _ =
  Bottom

complement :
  {A : Set} ->
  Predicate A ->
  Predicate A
complement S x =
  Not (S x)

countableUnion :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Predicate A
countableUnion sets x =
  Exists Nat (\ n -> sets n x)

Subset :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
Subset {A} S T =
  (x : A) ->
  S x ->
  T x

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint {A} sets =
  (i j : Nat) ->
  i != j ->
  (x : A) ->
  sets i x ->
  sets j x ->
  Bottom

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

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

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
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

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : Predicate R) ->
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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

successorInt : Int -> Int
successorInt (pos n) =
  pos (suc n)
successorInt (negsuc zero) =
  pos zero
successorInt (negsuc (suc n)) =
  negsuc n

doubleInt : Int -> Int
doubleInt (pos n) =
  pos (n + n)
doubleInt (negsuc n) =
  negsuc (suc (n + n))

record StandardFloor
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    floor : R -> Int

    floor-lower :
      (x : R) ->
      lessOrEqual reals
        (fromInt reals (floor x))
        x
    floor-upper :
      (x : R) ->
      StrictLess reals
        x
        (fromInt reals (successorInt (floor x)))
    floor-unique :
      (x : R) ->
      (z : Int) ->
      lessOrEqual reals (fromInt reals z) x ->
      StrictLess reals x (fromInt reals (successorInt z)) ->
      floor x == z

open StandardFloor

HalfOpen :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Predicate R
HalfOpen reals lower upper x =
  lessOrEqual reals lower x
  and
  StrictLess reals x upper

data ExtendedNonnegative
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set where
  finiteE   : R -> ExtendedNonnegative reals
  infinityE : ExtendedNonnegative reals

NonnegativeExtended :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  ExtendedNonnegative reals ->
  Set
NonnegativeExtended reals (finiteE value) =
  lessOrEqual reals (zeroR reals) value
NonnegativeExtended reals infinityE =
  Top

LessOrEqualE :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  ExtendedNonnegative reals ->
  ExtendedNonnegative reals ->
  Set
LessOrEqualE reals (finiteE x) (finiteE y) =
  lessOrEqual reals x y
LessOrEqualE reals (finiteE x) infinityE =
  Top
LessOrEqualE reals infinityE (finiteE y) =
  Bottom
LessOrEqualE reals infinityE infinityE =
  Top

addE :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  ExtendedNonnegative reals ->
  ExtendedNonnegative reals ->
  ExtendedNonnegative reals
addE reals (finiteE x) (finiteE y) =
  finiteE (add reals x y)
addE reals infinityE y =
  infinityE
addE reals (finiteE x) infinityE =
  infinityE

sumFirstE :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (Nat -> ExtendedNonnegative reals) ->
  Nat ->
  ExtendedNonnegative reals
sumFirstE reals terms zero =
  finiteE (zeroR reals)
sumFirstE reals terms (suc n) =
  addE reals
    (sumFirstE reals terms n)
    (terms n)

record IsCountableSum
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (terms : Nat -> ExtendedNonnegative reals)
  (total : ExtendedNonnegative reals) : Set1 where
  field
    partial-sums-below :
      (n : Nat) ->
      LessOrEqualE reals
        (sumFirstE reals terms n)
        total
    least-upper-bound :
      (bound : ExtendedNonnegative reals) ->
      ((n : Nat) ->
        LessOrEqualE reals
          (sumFirstE reals terms n)
          bound) ->
      LessOrEqualE reals total bound

record StandardLebesgueMeasure
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    measurable : Predicate R -> Set
    measure : Predicate R -> ExtendedNonnegative reals

    measurable-empty :
      measurable emptySet
    measurable-complement :
      (S : Predicate R) ->
      measurable S ->
      measurable (complement S)
    measurable-countable-union :
      (sets : Nat -> Predicate R) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (countableUnion sets)
    measurable-congruent :
      (S T : Predicate R) ->
      ((x : R) -> Iff (S x) (T x)) ->
      measurable S ->
      measurable T
    measurable-open-ray :
      (endpoint : R) ->
      measurable (\ x -> StrictLess reals endpoint x)
    measurable-complete :
      (N S : Predicate R) ->
      measurable N ->
      measure N == finiteE (zeroR reals) ->
      Subset S N ->
      measurable S

    measure-congruent :
      (S T : Predicate R) ->
      ((x : R) -> Iff (S x) (T x)) ->
      measure S == measure T
    measure-empty :
      measure emptySet == finiteE (zeroR reals)
    measure-nonnegative :
      (S : Predicate R) ->
      measurable S ->
      NonnegativeExtended reals (measure S)
    measure-half-open :
      (lower upper : R) ->
      lessOrEqual reals lower upper ->
      measure (HalfOpen reals lower upper) ==
      finiteE (subtract reals upper lower)
    measure-countable-additivity :
      (sets : Nat -> Predicate R) ->
      ((n : Nat) -> measurable (sets n)) ->
      PairwiseDisjoint sets ->
      IsCountableSum reals
        (\ n -> measure (sets n))
        (measure (countableUnion sets))
    measure-complete-null-subset :
      (N S : Predicate R) ->
      measurable N ->
      measure N == finiteE (zeroR reals) ->
      Subset S N ->
      measure S == finiteE (zeroR reals)

open StandardLebesgueMeasure

module Putnam1971B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (flooring : StandardFloor reals)
  (lebesgue : StandardLebesgueMeasure reals) where

  targetSet : R -> Predicate R
  targetSet T t =
    lessOrEqual reals T t
    and
    floor flooring t ==
      doubleInt (floor flooring (subtract reals t T))

  proposition : Set
  proposition =
    (T : R) ->
    StrictLess reals (zeroR reals) T ->
    measure lebesgue (targetSet T) ==
      finiteE (oneR reals)

putnam-1971-b3 : Set1
putnam-1971-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (flooring : StandardFloor reals) ->
  (lebesgue : StandardLebesgueMeasure reals) ->
  Putnam1971B3Statement.proposition reals flooring lebesgue
