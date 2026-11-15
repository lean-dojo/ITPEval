-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_a2
-- (putnambench__agda__putnam_2022_a2): the largest possible number of
-- negative coefficients in the square of a real polynomial of degree n,
-- for n at least 2, is 2n - 2. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

infix 4 _!=_ _<=N_ _<N_
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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

record PolynomialOfDegree
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (degree : Nat) :
  Set where

  field
    coefficient :
      Nat ->
      R
    coefficients-above-degree :
      (k : Nat) ->
      degree <N k ->
      coefficient k == zeroR reals
    leading-coefficient-nonzero :
      coefficient degree != zeroR reals

open PolynomialOfDegree

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

squareCoefficient :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {degree : Nat} ->
  PolynomialOfDegree reals degree ->
  Nat ->
  R
squareCoefficient reals polynomial k =
  sumFirst reals (suc k)
    (\ i ->
      multiply reals
        (coefficient polynomial i)
        (coefficient polynomial (k - i)))

data NegativeCountThrough
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (terms : Nat -> R) :
  Nat ->
  Nat ->
  Set where

  count-none :
    NegativeCountThrough reals terms zero zero

  count-negative :
    {length count : Nat} ->
    NegativeCountThrough reals terms length count ->
    StrictLess reals (terms length) (zeroR reals) ->
    NegativeCountThrough reals terms (suc length) (suc count)

  count-nonnegative :
    {length count : Nat} ->
    NegativeCountThrough reals terms length count ->
    lessOrEqual reals (zeroR reals) (terms length) ->
    NegativeCountThrough reals terms (suc length) count

record IsMaximumNegativeCount
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (degree maximum : Nat) :
  Set where

  field
    attained :
      Exists (PolynomialOfDegree reals degree)
        (\ polynomial ->
          NegativeCountThrough reals
            (squareCoefficient reals polynomial)
            (suc (degree + degree))
            maximum)

    upper-bound :
      (polynomial : PolynomialOfDegree reals degree) ->
      (count : Nat) ->
      NegativeCountThrough reals
        (squareCoefficient reals polynomial)
        (suc (degree + degree))
        count ->
      count <=N maximum

twoN : Nat
twoN =
  suc (suc zero)

putnam-2022-a2-solution : Nat -> Nat
putnam-2022-a2-solution n =
  (n + n) - twoN

putnam-2022-a2 : Set1
putnam-2022-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  twoN <=N n ->
  IsMaximumNegativeCount reals n
    (putnam-2022-a2-solution n)
