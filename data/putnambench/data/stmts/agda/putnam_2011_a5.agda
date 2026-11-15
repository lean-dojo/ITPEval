-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_a5
-- (putnambench__agda__putnam_2011_a5): twice continuously differentiable real
-- functions F and g, with F vanishing on the diagonal, g positive,
-- x^2*g(x) <= 1, and grad F(u,v) parallel to (g(u), -g(v)), have an O(1/n)
-- small value among any n+1 real inputs. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

open CompleteOrderedRealField

twoN : Nat
twoN =
  suc (suc zero)

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

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

ContinuousAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
ContinuousAt {R} reals function point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        CloseTo reals
          (function point)
          epsilon
          (function x)))

Continuous :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
Continuous {R} reals function =
  (point : R) ->
  ContinuousAt reals function point

ContinuousAt2 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R -> R) ->
  R ->
  R ->
  Set
ContinuousAt2 {R} reals function pointU pointV =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((u v : R) ->
        CloseTo reals pointU delta u ->
        CloseTo reals pointV delta v ->
        CloseTo reals
          (function pointU pointV)
          epsilon
          (function u v)))

Continuous2 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R -> R) ->
  Set
Continuous2 {R} reals function =
  (u v : R) ->
  ContinuousAt2 reals function u v

differenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point x =
  divide reals
    (subtract reals (function x) (function point))
    (subtract reals x point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

record TwiceContinuouslyDifferentiable1
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    firstDerivative secondDerivative : R -> R

    function-continuous :
      Continuous reals function
    first-derivative-correct :
      (x : R) ->
      DerivativeAt reals
        function
        x
        (firstDerivative x)
    first-derivative-continuous :
      Continuous reals firstDerivative
    second-derivative-correct :
      (x : R) ->
      DerivativeAt reals
        firstDerivative
        x
        (secondDerivative x)
    second-derivative-continuous :
      Continuous reals secondDerivative

record TwiceContinuouslyDifferentiable2
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R -> R) :
  Set where

  field
    firstPartialU firstPartialV : R -> R -> R
    secondPartialUU secondPartialUV : R -> R -> R
    secondPartialVU secondPartialVV : R -> R -> R

    function-continuous :
      Continuous2 reals function

    first-partial-u-correct :
      (u v : R) ->
      DerivativeAt reals
        (\ x -> function x v)
        u
        (firstPartialU u v)
    first-partial-v-correct :
      (u v : R) ->
      DerivativeAt reals
        (function u)
        v
        (firstPartialV u v)
    first-partial-u-continuous :
      Continuous2 reals firstPartialU
    first-partial-v-continuous :
      Continuous2 reals firstPartialV

    second-partial-uu-correct :
      (u v : R) ->
      DerivativeAt reals
        (\ x -> firstPartialU x v)
        u
        (secondPartialUU u v)
    second-partial-uv-correct :
      (u v : R) ->
      DerivativeAt reals
        (firstPartialU u)
        v
        (secondPartialUV u v)
    second-partial-vu-correct :
      (u v : R) ->
      DerivativeAt reals
        (\ x -> firstPartialV x v)
        u
        (secondPartialVU u v)
    second-partial-vv-correct :
      (u v : R) ->
      DerivativeAt reals
        (firstPartialV u)
        v
        (secondPartialVV u v)

    second-partial-uu-continuous :
      Continuous2 reals secondPartialUU
    second-partial-uv-continuous :
      Continuous2 reals secondPartialUV
    second-partial-vu-continuous :
      Continuous2 reals secondPartialVU
    second-partial-vv-continuous :
      Continuous2 reals secondPartialVV

open TwiceContinuouslyDifferentiable2

putnam-2011-a5 : Set1
putnam-2011-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (F : R -> R -> R) ->
  (g : R -> R) ->
  (smoothF : TwiceContinuouslyDifferentiable2 reals F) ->
  TwiceContinuouslyDifferentiable1 reals g ->
  ((u : R) ->
    F u u == zeroR reals) ->
  ((x : R) ->
    StrictLess reals (zeroR reals) (g x)
    and
    lessOrEqual reals
      (multiply reals
        (square reals x)
        (g x))
      (oneR reals)) ->
  ((u v : R) ->
    Exists R
      (\ c ->
        (firstPartialU smoothF u v ==
          multiply reals c (g u))
        and
        (firstPartialV smoothF u v ==
          multiply reals c (negate reals (g v))))) ->
  Exists R
    (\ C ->
      (n : Nat) ->
      twoN <=N n ->
      (x : Fin (suc n) -> R) ->
      Exists (Fin (suc n))
        (\ i ->
          Exists (Fin (suc n))
            (\ j ->
              i != j
              and
              lessOrEqual reals
                (absoluteValue reals
                  (F (x i) (x j)))
                (divide reals
                  C
                  (fromNat reals n)))))
