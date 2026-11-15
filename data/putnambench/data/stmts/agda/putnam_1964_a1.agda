-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_a1:
-- six distinct points in the real plane have longest-to-shortest pairwise
-- distance ratio at least the square root of three. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
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

six : Nat
six = suc five

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    supremum infimum : (R -> Set) -> R

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

    supremum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      ((x : R) ->
        P x ->
        lessOrEqual x (supremum P))
      and
      ((upper : R) ->
        ((x : R) -> P x -> lessOrEqual x upper) ->
        lessOrEqual (supremum P) upper)

    infimum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ lower ->
          (x : R) ->
          P x ->
          lessOrEqual lower x) ->
      ((x : R) ->
        P x ->
        lessOrEqual (infimum P) x)
      and
      ((lower : R) ->
        ((x : R) -> P x -> lessOrEqual lower x) ->
        lessOrEqual lower (infimum P))

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

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  squareRoot reals (squaredDistance reals p q)

module Putnam1964A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Plane : Set
  Plane = Point R

  Subset : Set1
  Subset = Plane -> Set

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

  PairwiseDistance : Subset -> R -> Set
  PairwiseDistance A d =
    Exists Plane
      (\ a ->
        Exists Plane
          (\ b ->
            A a
            and
            A b
            and
            a != b
            and
            d == distance reals a b))

  proposition : Set1
  proposition =
    (A : Subset) ->
    HasCardinality A six ->
    lessOrEqual reals
      (squareRoot reals (fromNat reals three))
      (divide reals
        (supremum reals (PairwiseDistance A))
        (infimum reals (PairwiseDistance A)))

putnam-1964-a1 : Set1
putnam-1964-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1964A1Statement.proposition reals
