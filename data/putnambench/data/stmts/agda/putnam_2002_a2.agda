-- Statement-only formalization of PutnamBench corpus artifact putnam_2002_a2:
-- among any five points on the unit sphere in real three-space, four lie in
-- one closed hemisphere. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

three : Nat
three =
  suc (suc (suc zero))

four : Nat
four =
  suc three

five : Nat
five =
  suc four

Point :
  Set ->
  Set
Point R =
  Fin three -> R

Subset :
  Set ->
  Set1
Subset A =
  A -> Set

ContainedIn :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Set
ContainedIn S T =
  (x : _) ->
  S x ->
  T x

Intersection :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Subset A
Intersection S T x =
  S x and T x

record HasCardinality
  {A : Set}
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
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record HasAtLeastCardinality
  {A : Set}
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
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

VectorEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
VectorEqual u v =
  (i : Fin three) ->
  u i == v i

ZeroVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R
ZeroVector reals i =
  zeroR reals

VectorNonzero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Set
VectorNonzero reals v =
  Not (VectorEqual v (ZeroVector reals))

dot :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
dot reals u v =
  add reals
    (multiply reals (u fzero) (v fzero))
    (add reals
      (multiply reals (u (fsuc fzero)) (v (fsuc fzero)))
      (multiply reals
        (u (fsuc (fsuc fzero)))
        (v (fsuc (fsuc fzero)))))

UnitSphere :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Subset (Point R)
UnitSphere reals point =
  dot reals point point == oneR reals

ClosedHemisphere :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Subset (Point R)
ClosedHemisphere reals normal point =
  lessOrEqual reals
    (zeroR reals)
    (dot reals point normal)

putnam-2002-a2 : Set1
putnam-2002-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (S : Subset (Point R)) ->
  ContainedIn S (UnitSphere reals) ->
  HasCardinality S five ->
  Exists (Point R)
    (\ normal ->
      VectorNonzero reals normal
      and
      HasAtLeastCardinality
        (Intersection S (ClosedHemisphere reals normal))
        four)
