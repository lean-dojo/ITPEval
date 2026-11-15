-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_b4
-- (putnambench__agda__putnam_2006_b4): the maximum number of Boolean-cube
-- vertices in a k-dimensional real linear subspace of R^n is 2^k. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2006B4 where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

Positive : Nat -> Set
Positive n =
  suc zero <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Predicate : Set -> Set1
Predicate A =
  A -> Set

record HasCardinality
  {a r p : Level}
  {A : Set a}
  (equivalent : A -> A -> Set r)
  (member : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ r ⊔ p) where

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
      (leftIndex rightIndex : Fin cardinality) ->
      equivalent
        (enumerate leftIndex)
        (enumerate rightIndex) ->
      leftIndex == rightIndex

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
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) ==
      multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))

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

Vector : Set -> Nat -> Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} leftVector rightVector =
  (coordinate : Fin n) ->
  leftVector coordinate == rightVector coordinate

zeroVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  Vector R n
zeroVector reals n coordinate =
  zeroR reals

addVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Vector R n
addVector reals leftVector rightVector coordinate =
  add reals
    (leftVector coordinate)
    (rightVector coordinate)

scaleVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  R ->
  Vector R n ->
  Vector R n
scaleVector reals scalar vector coordinate =
  multiply reals scalar (vector coordinate)

record Subspace
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (n : Nat) :
  Set1 where

  field
    member :
      Predicate (Vector R n)

    zero-member :
      member (zeroVector reals n)

    add-member :
      (leftVector rightVector : Vector R n) ->
      member leftVector ->
      member rightVector ->
      member (addVector reals leftVector rightVector)

    scale-member :
      (scalar : R) ->
      (vector : Vector R n) ->
      member vector ->
      member (scaleVector reals scalar vector)

open Subspace

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  (Fin n -> R) ->
  R
sumFin reals zero terms =
  zeroR reals
sumFin reals (suc n) terms =
  add reals
    (terms fzero)
    (sumFin reals n
      (\ index ->
        terms (fsuc index)))

linearCombination :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n k : Nat} ->
  (Fin k -> Vector R n) ->
  (Fin k -> R) ->
  Vector R n
linearCombination reals {k = k} basis coefficients coordinate =
  sumFin reals k
    (\ index ->
      multiply reals
        (coefficients index)
        (basis index coordinate))

LinearIndependent :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n k : Nat} ->
  (Fin k -> Vector R n) ->
  Set
LinearIndependent reals {n = n} basis =
  (coefficients : Fin _ -> _) ->
  ((coordinate : Fin n) ->
    linearCombination reals basis coefficients coordinate ==
    zeroR reals) ->
  (index : Fin _) ->
  coefficients index == zeroR reals

Spans :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n k : Nat} ->
  Subspace reals n ->
  (Fin k -> Vector R n) ->
  Set
Spans reals {n = n} subspace basis =
  (vector : Vector _ n) ->
  member subspace vector ->
  Exists (Fin _ -> _)
    (\ coefficients ->
      (coordinate : Fin n) ->
      linearCombination reals basis coefficients coordinate ==
      vector coordinate)

HasDimension :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  Subspace reals n ->
  Nat ->
  Set
HasDimension reals subspace k =
  Exists (Fin k -> Vector _ _)
    (\ basis ->
      ((index : Fin k) ->
        member subspace (basis index))
      and
      LinearIndependent reals basis
      and
      Spans reals subspace basis)

BooleanCube :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  Predicate (Vector R n)
BooleanCube reals n vector =
  (coordinate : Fin n) ->
  vector coordinate == zeroR reals
  or
  vector coordinate == oneR reals

CubeIntersection :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  Subspace reals n ->
  Predicate (Vector R n)
CubeIntersection reals {n} subspace vector =
  BooleanCube reals n vector
  and
  member subspace vector

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

powerOfTwo : Nat -> Nat
powerOfTwo zero =
  oneN
powerOfTwo (suc exponent) =
  twoN * powerOfTwo exponent

module Putnam2006B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  IntersectionHasCardinality :
    {n : Nat} ->
    Subspace reals n ->
    Nat ->
    Set
  IntersectionHasCardinality {n} subspace cardinality =
    HasCardinality
      (VectorEqual {R = R} {n = n})
      (CubeIntersection reals subspace)
      cardinality

  AttainsMaximum :
    (n k : Nat) ->
    Set1
  AttainsMaximum n k =
    Exists (Subspace reals n)
      (\ subspace ->
        HasDimension reals subspace k
        and
        IntersectionHasCardinality
          subspace
          (powerOfTwo k))

  IsUpperBound :
    (n k : Nat) ->
    Set1
  IsUpperBound n k =
    (subspace : Subspace reals n) ->
    HasDimension reals subspace k ->
    (cardinality : Nat) ->
    IntersectionHasCardinality subspace cardinality ->
    cardinality <=N powerOfTwo k

  proposition : Set1
  proposition =
    (n k : Nat) ->
    Positive n ->
    k <=N n ->
    AttainsMaximum n k
    and
    IsUpperBound n k

putnam-2006-b4 : Set1
putnam-2006-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2006B4Statement.proposition reals
