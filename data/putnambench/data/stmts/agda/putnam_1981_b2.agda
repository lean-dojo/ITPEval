-- Statement-only formalization of PutnamBench corpus artifact putnam_1981_b2:
-- the minimum of a four-term sum of squared successive relative increments
-- over real numbers 1 <= r <= s <= t <= 4 is 12 - 8 * sqrt 2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1981B2 where

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

module Putnam1981B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  twoN : Nat
  twoN =
    suc (suc zero)

  fourN : Nat
  fourN =
    twoN + twoN

  eightN : Nat
  eightN =
    fourN + fourN

  twelveN : Nat
  twelveN =
    eightN + fourN

  two four eight twelve : R
  two =
    fromNat reals twoN
  four =
    fromNat reals fourN
  eight =
    fromNat reals eightN
  twelve =
    fromNat reals twelveN

  Feasible : R -> R -> R -> Set
  Feasible r s t =
    lessOrEqual reals (oneR reals) r
    and
    lessOrEqual reals r s
    and
    lessOrEqual reals s t
    and
    lessOrEqual reals t four

  objective : R -> R -> R -> R
  objective r s t =
    add reals
      (add reals
        (square reals
          (subtract reals r (oneR reals)))
        (square reals
          (subtract reals
            (divide reals s r)
            (oneR reals))))
      (add reals
        (square reals
          (subtract reals
            (divide reals t s)
            (oneR reals)))
        (square reals
          (subtract reals
            (divide reals four t)
            (oneR reals))))

  solution : R
  solution =
    subtract reals
      twelve
      (multiply reals eight (squareRoot reals two))

  IsMinimumValue : R -> Set
  IsMinimumValue minimum =
    ((r s t : R) ->
      Feasible r s t ->
      lessOrEqual reals minimum (objective r s t))
    and
    Exists R
      (\ r ->
        Exists R
          (\ s ->
            Exists R
              (\ t ->
                Feasible r s t
                and
                minimum == objective r s t)))

  proposition : Set
  proposition =
    IsMinimumValue solution

putnam-1981-b2 : Set1
putnam-1981-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1981B2Statement.proposition reals
