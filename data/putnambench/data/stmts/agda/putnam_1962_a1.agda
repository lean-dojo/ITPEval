-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_a1:
-- among five points in the real plane with no three collinear, some four are
-- the vertices of a convex quadrilateral. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : {a : Level} -> Set a -> Set a
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

five : Nat
five = suc four

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open CompleteOrderedField
open Point

module Putnam1962A1Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  Plane : Set
  Plane = Point R

  Subset : Set1
  Subset = Plane -> Set

  SubsetOf : Subset -> Subset -> Set
  SubsetOf A B =
    (p : Plane) -> A p -> B p

  record HasCardinality (A : Subset) (n : Nat) : Set where
    field
      enumerate :
        Fin n -> Plane
      enumerated-member :
        (i : Fin n) -> A (enumerate i)
      enumeration-complete :
        (p : Plane) ->
        A p ->
        Exists (Fin n) (\ i -> p == enumerate i)
      enumeration-injective :
        (i j : Fin n) ->
        enumerate i == enumerate j ->
        i == j

  subtract : R -> R -> R
  subtract x y =
    add reals x (negate reals y)

  determinant-zero : Plane -> Plane -> Plane -> Set
  determinant-zero a b c =
    multiply reals
      (subtract (x-coordinate a) (x-coordinate c))
      (subtract (y-coordinate b) (y-coordinate c))
    ==
    multiply reals
      (subtract (y-coordinate a) (y-coordinate c))
      (subtract (x-coordinate b) (x-coordinate c))

  Collinear : Subset -> Set
  Collinear A =
    (a b c : Plane) ->
    A a ->
    A b ->
    A c ->
    determinant-zero a b c

  affineCombination : R -> Plane -> Plane -> Plane
  affineCombination coefficient p q =
    point
      (add reals
        (multiply reals coefficient (x-coordinate p))
        (multiply reals
          (subtract (oneR reals) coefficient)
          (x-coordinate q)))
      (add reals
        (multiply reals coefficient (y-coordinate p))
        (multiply reals
          (subtract (oneR reals) coefficient)
          (y-coordinate q)))

  Convex : Subset -> Set
  Convex A =
    (p q : Plane) ->
    A p ->
    A q ->
    (coefficient : R) ->
    lessOrEqual reals (zeroR reals) coefficient ->
    lessOrEqual reals coefficient (oneR reals) ->
    A (affineCombination coefficient p q)

  ConvexHull : Subset -> Plane -> Set1
  ConvexHull A p =
    (C : Subset) ->
    SubsetOf A C ->
    Convex C ->
    C p

  remove : Subset -> Plane -> Subset
  remove A removed p =
    A p and p != removed

  proposition : Set1
  proposition =
    (S : Subset) ->
    HasCardinality S five ->
    ((s : Subset) ->
      SubsetOf s S ->
      HasCardinality s three ->
      Not (Collinear s)) ->
    Exists Subset
      (\ T ->
        SubsetOf T S
        and
        HasCardinality T four
        and
        Not
          (Exists Plane
            (\ t ->
              T t
              and
              ConvexHull (remove T t) t)))

putnam-1962-a1 : Set1
putnam-1962-a1 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1962A1Statement.proposition reals
