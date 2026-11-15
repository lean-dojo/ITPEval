-- Statement-only formalization of PutnamBench corpus artifact putnam_1963_b6:
-- iterating the closed-segment hull of a nonempty subset of a real Euclidean
-- space of dimension one through three stabilizes after the second iterate.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
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
      Either (lessOrEqual x y) (lessOrEqual y x)
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
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

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
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector : Set -> Nat -> Set
Vector R d =
  Fin d -> R

Subset : Set -> Nat -> Set1
Subset R d =
  Vector R d -> Set

SetEqual :
  {R : Set} ->
  {d : Nat} ->
  Subset R d ->
  Subset R d ->
  Set
SetEqual {R} {d} A B =
  Both
    ((x : Vector R d) -> A x -> B x)
    ((x : Vector R d) -> B x -> A x)

Nonempty :
  {R : Set} ->
  {d : Nat} ->
  Subset R d ->
  Set
Nonempty {R} {d} A =
  Exists (Vector R d) A

affineCombination :
  {R : Set} ->
  {d : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R d ->
  Vector R d ->
  Vector R d
affineCombination reals t p q i =
  add reals
    (multiply reals t (p i))
    (multiply reals
      (subtract reals (oneR reals) t)
      (q i))

ClosedSegment :
  {R : Set} ->
  {d : Nat} ->
  CompleteOrderedField R ->
  Vector R d ->
  Vector R d ->
  Vector R d ->
  Set
ClosedSegment {R} {d} reals p q x =
  Exists R
    (\ t ->
      Both
        (lessOrEqual reals (zeroR reals) t)
        (Both
          (lessOrEqual reals t (oneR reals))
          ((i : Fin d) ->
            x i == affineCombination reals t p q i)))

SegmentHull :
  {R : Set} ->
  {d : Nat} ->
  CompleteOrderedField R ->
  Subset R d ->
  Subset R d
SegmentHull {R} {d} reals A x =
  Exists (Vector R d)
    (\ p ->
      Both
        (A p)
        (Exists (Vector R d)
          (\ q ->
            Both
              (A q)
              (ClosedSegment reals p q x))))

putnam-1963-b6 : Set1
putnam-1963-b6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (d : Nat) ->
  Both (1 <=N d) (d <=N 3) ->
  (A : Nat -> Subset R d) ->
  Nonempty (A zero) ->
  ((n : Nat) ->
    SetEqual
      (A (suc n))
      (SegmentHull reals (A n))) ->
  (n : Nat) ->
  2 <=N n ->
  SetEqual (A n) (A (suc n))
