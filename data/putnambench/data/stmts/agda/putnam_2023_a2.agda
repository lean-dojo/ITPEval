-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_a2
-- (putnambench__agda__putnam_2023_a2): the two additional reciprocal
-- interpolation solutions of a monic real polynomial of even degree.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Positive : Nat -> Set
Positive n =
  oneN <=N n

Even : Nat -> Set
Even n =
  Exists Nat
    (\ half -> n == half + half)

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

module Putnam2023A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Polynomial : Set
  Polynomial =
    List R

  coefficient : Polynomial -> Nat -> R
  coefficient [] n =
    zeroR reals
  coefficient (c ∷ coefficients) zero =
    c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  evaluate : Polynomial -> R -> R
  evaluate [] x =
    zeroR reals
  evaluate (c ∷ coefficients) x =
    add reals c
      (multiply reals x (evaluate coefficients x))

  MonicOfDegree : Polynomial -> Nat -> Set
  MonicOfDegree p degree =
    coefficient p degree == oneR reals
    and
    ((index : Nat) ->
      degree <N index ->
      coefficient p index == zeroR reals)

  InInterpolationSet : Nat -> R -> Set
  InInterpolationSet n x =
    Exists Nat
      (\ magnitude ->
        oneN <=N magnitude
        and
        magnitude <=N n
        and
        (x == fromNat reals magnitude
        or
        x == negate reals (fromNat reals magnitude)))

  ReciprocalInterpolation : Nat -> Polynomial -> Set
  ReciprocalInterpolation n p =
    (x : R) ->
    InInterpolationSet n x ->
    evaluate p (divide reals (oneR reals) x) ==
    square reals x

  OtherSolution : Nat -> Polynomial -> R -> Set
  OtherSolution n p x =
    x != zeroR reals
    and
    evaluate p (divide reals (oneR reals) x) ==
      square reals x
    and
    Not (InInterpolationSet n x)

  ExplicitSolution : Nat -> R -> Set
  ExplicitSolution n x =
    let
      reciprocal-factorial =
        divide reals
          (oneR reals)
          (fromNat reals (factorial n))
    in
    x == reciprocal-factorial
    or
    x == negate reals reciprocal-factorial

  proposition : Set
  proposition =
    (n : Nat) ->
    Positive n ->
    Even n ->
    (p : Polynomial) ->
    MonicOfDegree p (twoN * n) ->
    ReciprocalInterpolation n p ->
    (x : R) ->
    OtherSolution n p x iff ExplicitSolution n x

putnam-2023-a2 : Set1
putnam-2023-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2023A2Statement.proposition reals
