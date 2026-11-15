-- Statement-only formalization of PutnamBench corpus artifact putnam_2008_b3
-- (putnambench__agda__putnam_2008_b3): the largest radius of a circle
-- contained in a four-dimensional hypercube of side length one is
-- sqrt(2) / 2. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2008B3 where

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
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
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

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  squareRoot reals (square reals x)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

twoN : Nat
twoN =
  suc (suc zero)

fourN : Nat
fourN =
  suc (suc (suc (suc zero)))

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  fromNat reals twoN

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  divide reals (oneR reals) (two reals)

Vector : Set -> Nat -> Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) ->
  x i == y i

zeroVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  Vector R n
zeroVector reals _ =
  zeroR reals

addVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
addVector reals x y i =
  add reals (x i) (y i)

scaleVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  R ->
  Vector R n ->
  Vector R n
scaleVector reals scalar x i =
  multiply reals scalar (x i)

sumFin :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  (Fin n -> R) ->
  R
sumFin {n = zero} reals values =
  zeroR reals
sumFin {n = suc n} reals values =
  add reals
    (values fzero)
    (sumFin reals
      (\ i ->
        values (fsuc i)))

squaredNorm :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  Vector R n ->
  R
squaredNorm reals x =
  sumFin reals
    (\ i ->
      square reals (x i))

norm :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  Vector R n ->
  R
norm reals x =
  squareRoot reals (squaredNorm reals x)

LinearCombination :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  R ->
  Vector R n ->
  R ->
  Vector R n ->
  Vector R n
LinearCombination reals s p t q =
  addVector reals
    (scaleVector reals s p)
    (scaleVector reals t q)

LinearlyIndependentPair :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  Vector R n ->
  Vector R n ->
  Set
LinearlyIndependentPair {R} {n} reals p q =
  (s t : R) ->
  VectorEqual
    (LinearCombination reals s p t q)
    (zeroVector reals) ->
  s == zeroR reals and t == zeroR reals

InUnitHypercube4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R fourN ->
  Set
InUnitHypercube4 reals x =
  (i : Fin fourN) ->
  lessOrEqual reals
    (absoluteValue reals (x i))
    (half reals)

ContainsCircle :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
ContainsCircle {R} reals radius =
  Exists (Vector R fourN)
    (\ center ->
      Exists (Vector R fourN)
        (\ p ->
          Exists (Vector R fourN)
            (\ q ->
              LinearlyIndependentPair reals p q
              and
              ((s t : R) ->
                norm reals
                  (LinearCombination reals s p t q)
                  == radius ->
                InUnitHypercube4 reals
                  (addVector reals
                    center
                    (LinearCombination reals s p t q))))))

putnam-2008-b3-solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
putnam-2008-b3-solution reals =
  divide reals
    (squareRoot reals (two reals))
    (two reals)

putnam-2008-b3 : Set1
putnam-2008-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  ContainsCircle reals (putnam-2008-b3-solution reals)
  and
  ((radius : R) ->
    StrictLess reals
      (putnam-2008-b3-solution reals)
      radius ->
    Not (ContainsCircle reals radius))
