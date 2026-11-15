-- Statement-only formalization of PutnamBench corpus artifact putnam_1971_a1:
-- every set of nine lattice points in three-dimensional real space has a
-- lattice point in the interior of a segment joining two distinct members.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

sixN : Nat
sixN =
  suc fiveN

sevenN : Nat
sevenN =
  suc sixN

eightN : Nat
eightN =
  suc sevenN

nineN : Nat
nineN =
  suc eightN

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
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
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
      (x : R) -> lessOrEqual x x
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
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
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

record LatticePoint : Set where
  constructor lattice-point
  field
    x-coordinate : Int
    y-coordinate : Int
    z-coordinate : Int

open LatticePoint

LatticeSubset : Set1
LatticeSubset =
  LatticePoint -> Set

record HasCardinality
  (S : LatticeSubset)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      LatticePoint
    enumerated-member :
      (index : Fin cardinality) ->
      S (enumerate index)
    enumeration-complete :
      (point : LatticePoint) ->
      S point ->
      Exists (Fin cardinality)
        (\ index -> point == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

InteriorSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  LatticePoint ->
  LatticePoint ->
  Int ->
  Int ->
  Int ->
  Set
InteriorSegment reals P Q x y z =
  Exists _
    (\ t ->
      StrictLess reals (zeroR reals) t
      and
      StrictLess reals t (oneR reals)
      and
      fromInt reals x ==
        add reals
          (multiply reals t (fromInt reals (x-coordinate P)))
          (multiply reals
            (subtract reals (oneR reals) t)
            (fromInt reals (x-coordinate Q)))
      and
      fromInt reals y ==
        add reals
          (multiply reals t (fromInt reals (y-coordinate P)))
          (multiply reals
            (subtract reals (oneR reals) t)
            (fromInt reals (y-coordinate Q)))
      and
      fromInt reals z ==
        add reals
          (multiply reals t (fromInt reals (z-coordinate P)))
          (multiply reals
            (subtract reals (oneR reals) t)
            (fromInt reals (z-coordinate Q))))

module Putnam1971A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set1
  proposition =
    (S : LatticeSubset) ->
    HasCardinality S nineN ->
    Exists Int
      (\ x ->
        Exists Int
          (\ y ->
            Exists Int
              (\ z ->
                Exists LatticePoint
                  (\ P ->
                    Exists LatticePoint
                      (\ Q ->
                        S P
                        and
                        S Q
                        and
                        P != Q
                        and
                        InteriorSegment reals P Q x y z)))))

putnam-1971-a1 : Set1
putnam-1971-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1971A1Statement.proposition reals
