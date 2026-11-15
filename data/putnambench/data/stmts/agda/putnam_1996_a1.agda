-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_a1
-- (putnambench__agda__putnam_1996_a1): the least area of a positive rectangle
-- that can pack every positive unit-sum-of-squares pair of side lengths is
-- (1 + sqrt 2) / 2. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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

record StandardReal (R : Set) : Set1 where
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
      (x y : R) -> Either (lessOrEqual x y) (lessOrEqual y x)
    add-monotone :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-or-equal-one :
      lessOrEqual zeroR oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n
    fromNat-nonnegative :
      (n : Nat) -> lessOrEqual zeroR (fromNat n)

    square-root-nonnegative :
      (x : R) -> lessOrEqual zeroR (squareRoot x)
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
      squareRoot x == y

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open StandardReal

maximum :
  {R : Set} ->
  StandardReal R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left x-le-y =
  y
... | right y-le-x =
  x

minimum :
  {R : Set} ->
  StandardReal R ->
  R ->
  R ->
  R
minimum reals x y with order-total reals x y
... | left x-le-y =
  x
... | right y-le-x =
  y

square :
  {R : Set} ->
  StandardReal R ->
  R ->
  R
square reals x =
  multiply reals x x

divide :
  {R : Set} ->
  StandardReal R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  StandardReal R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both
    (lessOrEqual reals x y)
    (x != y)

solution :
  {R : Set} ->
  StandardReal R ->
  R
solution reals =
  divide reals
    (add reals
      (oneR reals)
      (squareRoot reals (fromNat reals 2)))
    (fromNat reals 2)

Packable :
  {R : Set} ->
  StandardReal R ->
  R ->
  R ->
  R ->
  R ->
  Set
Packable reals n1 n2 a1 a2 =
  Both
    (lessOrEqual reals
      (add reals n1 n2)
      (maximum reals a1 a2))
    (lessOrEqual reals
      (maximum reals n1 n2)
      (minimum reals a1 a2))

AProperty :
  {R : Set} ->
  StandardReal R ->
  R ->
  Set
AProperty {R} reals area =
  (n1 n2 : R) ->
  Both
    (StrictLess reals (zeroR reals) n1)
    (Both
      (StrictLess reals (zeroR reals) n2)
      (add reals
        (square reals n1)
        (square reals n2)
        == oneR reals)) ->
  Exists R
    (\ a1 ->
      Exists R
        (\ a2 ->
          Both
            (StrictLess reals (zeroR reals) a1)
            (Both
              (StrictLess reals (zeroR reals) a2)
              (Both
                (multiply reals a1 a2 == area)
                (Packable reals n1 n2 a1 a2)))))

putnam-1996-a1 : Set1
putnam-1996-a1 =
  (R : Set) ->
  (reals : StandardReal R) ->
  Both
    (AProperty reals (solution reals))
    ((area : R) ->
      AProperty reals area ->
      lessOrEqual reals (solution reals) area)
