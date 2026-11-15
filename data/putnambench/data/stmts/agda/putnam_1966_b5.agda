-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_b5:
-- every finite set of at least three real-plane points with no three collinear
-- is the vertex set of a simple closed polygon. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

record ExistsUniqueBy
  (A : Set)
  (equal : A -> A -> Set)
  (P : A -> Set) :
  Set where

  constructor unique-witness
  field
    unique-value    : A
    unique-property : P unique-value
    uniqueness :
      (other : A) ->
      P other ->
      equal other unique-value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

weakenFin : {n : Nat} -> Fin n -> Fin (suc n)
weakenFin {zero} ()
weakenFin {suc n} fzero =
  fzero
weakenFin {suc n} (fsuc i) =
  fsuc (weakenFin i)

advanceTail :
  {n : Nat} ->
  Fin (suc n) ->
  Fin (suc (suc n))
advanceTail {zero} fzero =
  fzero
advanceTail {suc n} fzero =
  fsuc (fsuc fzero)
advanceTail {suc n} (fsuc i) =
  fsuc (advanceTail i)

nextFin : {n : Nat} -> Fin n -> Fin n
nextFin {zero} ()
nextFin {suc zero} fzero =
  fzero
nextFin {suc (suc n)} fzero =
  fsuc fzero
nextFin {suc (suc n)} (fsuc i) =
  advanceTail i

three : Nat
three = suc (suc (suc zero))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
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

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  x-coordinate p == x-coordinate q
  and
  y-coordinate p == y-coordinate q

scalePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R
scalePoint reals t p =
  point
    (multiply reals t (x-coordinate p))
    (multiply reals t (y-coordinate p))

addPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
addPoint reals p q =
  point
    (add reals (x-coordinate p) (x-coordinate q))
    (add reals (y-coordinate p) (y-coordinate q))

affinePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R ->
  Point R
affinePoint reals t p q =
  addPoint reals
    (scalePoint reals (subtract reals (oneR reals) t) p)
    (scalePoint reals t q)

ClosedSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
ClosedSegment {R} reals p q x =
  Exists R
    (\ t ->
      lessOrEqual reals (zeroR reals) t
      and
      lessOrEqual reals t (oneR reals)
      and
      PointEqual x (affinePoint reals t p q))

doubleSignedArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
doubleSignedArea reals a b c =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiply reals
      (subtract reals (y-coordinate b) (y-coordinate a))
      (subtract reals (x-coordinate c) (x-coordinate a)))

Collinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Collinear reals a b c =
  doubleSignedArea reals a b c == zeroR reals

record FinitePointSet (R : Set) : Set1 where
  field
    cardinality : Nat
    member : Point R -> Set
    listing : Fin cardinality -> Point R

    member-invariant :
      (p q : Point R) ->
      PointEqual p q ->
      (member p -> member q) and (member q -> member p)

    listing-member :
      (i : Fin cardinality) ->
      member (listing i)

    listing-injective :
      (i j : Fin cardinality) ->
      PointEqual (listing i) (listing j) ->
      i == j

    member-listed :
      (p : Point R) ->
      member p ->
      Exists (Fin cardinality)
        (\ i -> PointEqual p (listing i))

open FinitePointSet

GeneralPosition :
  {R : Set} ->
  CompleteOrderedRealField R ->
  FinitePointSet R ->
  Set
GeneralPosition reals points =
  (a b c : Point _) ->
  member points a ->
  member points b ->
  member points c ->
  Not (PointEqual a b) ->
  Not (PointEqual b c) ->
  Not (PointEqual c a) ->
  Not (Collinear reals a b c)

EnumeratesExactlyOnce :
  {R : Set} ->
  (points : FinitePointSet R) ->
  (Fin (cardinality points) -> Point R) ->
  Set
EnumeratesExactlyOnce points vertices =
  (p : Point _) ->
  member points p ->
  ExistsUniqueBy
    (Fin (cardinality points))
    _==_
    (\ i -> PointEqual p (vertices i))

EdgesMeetOnlyAtEndpoints :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> Point R) ->
  Set
EdgesMeetOnlyAtEndpoints reals vertices =
  (i j : Fin _) ->
  i != j ->
  (intersection : Point _) ->
  ClosedSegment reals
    (vertices i)
    (vertices (nextFin i))
    intersection ->
  ClosedSegment reals
    (vertices j)
    (vertices (nextFin j))
    intersection ->
  PointEqual intersection (vertices i)
  or
  PointEqual intersection (vertices (nextFin i))
  or
  PointEqual intersection (vertices j)
  or
  PointEqual intersection (vertices (nextFin j))

module Putnam1966B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set1
  proposition =
    (points : FinitePointSet R) ->
    three <=N cardinality points ->
    GeneralPosition reals points ->
    Exists
      (Fin (cardinality points) -> Point R)
      (\ vertices ->
        EnumeratesExactlyOnce points vertices
        and
        EdgesMeetOnlyAtEndpoints reals vertices)

putnam-1966-b5 : Set1
putnam-1966-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1966B5Statement.proposition reals
