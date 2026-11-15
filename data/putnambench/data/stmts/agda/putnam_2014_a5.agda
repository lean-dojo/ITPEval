-- Statement-only formalization of PutnamBench corpus artifact putnam_2014_a5:
-- the polynomials P_n(x) = 1 + 2x + ... + n*x^(n-1) are relatively prime
-- for distinct positive indices. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2014A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

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
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
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

Polynomial : Set -> Set
Polynomial R =
  List R

coefficient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  R
coefficient reals [] n =
  zeroR reals
coefficient reals (c ∷ coefficients) zero =
  c
coefficient reals (c ∷ coefficients) (suc n) =
  coefficient reals coefficients n

PolynomialEqual :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Set
PolynomialEqual reals p q =
  (n : Nat) ->
  coefficient reals p n == coefficient reals q n

addPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
addPolynomial reals [] q =
  q
addPolynomial reals p [] =
  p
addPolynomial reals (a ∷ p) (b ∷ q) =
  add reals a b ∷ addPolynomial reals p q

scalePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Polynomial R ->
  Polynomial R
scalePolynomial reals scalar [] =
  []
scalePolynomial reals scalar (c ∷ coefficients) =
  multiply reals scalar c ∷
  scalePolynomial reals scalar coefficients

shiftPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R
shiftPolynomial reals p =
  zeroR reals ∷ p

multiplyPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
multiplyPolynomial reals [] q =
  []
multiplyPolynomial reals (a ∷ p) q =
  addPolynomial reals
    (scalePolynomial reals a q)
    (shiftPolynomial reals
      (multiplyPolynomial reals p q))

snoc :
  {A : Set} ->
  List A ->
  A ->
  List A
snoc [] x =
  x ∷ []
snoc (x ∷ xs) y =
  x ∷ snoc xs y

putnamPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Polynomial R
putnamPolynomial reals zero =
  []
putnamPolynomial reals (suc n) =
  snoc
    (putnamPolynomial reals n)
    (fromNat reals (suc n))

onePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R
onePolynomial reals =
  oneR reals ∷ []

RelativelyPrime :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Set
RelativelyPrime {R} reals p q =
  Exists (Polynomial R)
    (\ a ->
      Exists (Polynomial R)
        (\ b ->
          PolynomialEqual reals
            (addPolynomial reals
              (multiplyPolynomial reals a p)
              (multiplyPolynomial reals b q))
            (onePolynomial reals)))

putnam-2014-a5 : Set1
putnam-2014-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (j k : Nat) ->
  Positive j ->
  Positive k ->
  j != k ->
  RelativelyPrime reals
    (putnamPolynomial reals j)
    (putnamPolynomial reals k)
