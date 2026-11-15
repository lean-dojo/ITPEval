-- Statement-only formalization of PutnamBench corpus artifact putnam_1971_a4:
-- eventual strict positivity of every coefficient in the finite homogeneous
-- support of a parameterized bivariate polynomial. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1971A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) -> addR x zeroR == x
    add-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) -> multiplyR x oneR == x
    multiply-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedRealField

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

module PolynomialDefinitions
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Polynomial : Set
  Polynomial =
    Nat -> Nat -> R

  sumThrough : (Nat -> R) -> Nat -> R
  sumThrough f zero =
    f zero
  sumThrough f (suc n) =
    addR reals (sumThrough f n) (f (suc n))

  zeroPolynomial : Polynomial
  zeroPolynomial i j =
    zeroR reals

  constantPolynomial : R -> Polynomial
  constantPolynomial c zero zero =
    c
  constantPolynomial c zero (suc j) =
    zeroR reals
  constantPolynomial c (suc i) j =
    zeroR reals

  xVariable : Polynomial
  xVariable zero j =
    zeroR reals
  xVariable (suc zero) zero =
    oneR reals
  xVariable (suc zero) (suc j) =
    zeroR reals
  xVariable (suc (suc i)) j =
    zeroR reals

  yVariable : Polynomial
  yVariable zero zero =
    zeroR reals
  yVariable zero (suc zero) =
    oneR reals
  yVariable zero (suc (suc j)) =
    zeroR reals
  yVariable (suc i) j =
    zeroR reals

  addPolynomial : Polynomial -> Polynomial -> Polynomial
  addPolynomial p q i j =
    addR reals (p i j) (q i j)

  negatePolynomial : Polynomial -> Polynomial
  negatePolynomial p i j =
    negateR reals (p i j)

  subtractPolynomial : Polynomial -> Polynomial -> Polynomial
  subtractPolynomial p q =
    addPolynomial p (negatePolynomial q)

  scalePolynomial : R -> Polynomial -> Polynomial
  scalePolynomial c p i j =
    multiplyR reals c (p i j)

  multiplyPolynomial : Polynomial -> Polynomial -> Polynomial
  multiplyPolynomial p q i j =
    sumThrough
      (\ a ->
        sumThrough
          (\ b ->
            multiplyR reals
              (p a b)
              (q (i - a) (j - b)))
          j)
      i

  powerPolynomial : Polynomial -> Nat -> Polynomial
  powerPolynomial p zero =
    constantPolynomial (oneR reals)
  powerPolynomial p (suc n) =
    multiplyPolynomial (powerPolynomial p n) p

  twoR : R
  twoR =
    fromNatR reals (suc (suc zero))

  polynomialFamily : Nat -> R -> Polynomial
  polynomialFamily n delta =
    multiplyPolynomial
      (powerPolynomial
        (addPolynomial xVariable yVariable)
        n)
      (addPolynomial
        (subtractPolynomial
          (powerPolynomial xVariable (suc (suc zero)))
          (scalePolynomial
            (addR reals twoR (negateR reals delta))
            (multiplyPolynomial xVariable yVariable)))
        (powerPolynomial yVariable (suc (suc zero))))

  proposition : Set
  proposition =
    (epsilon : R) ->
    StrictLess reals (zeroR reals) epsilon ->
    StrictLess reals epsilon (oneR reals) ->
    Exists Nat
      (\ cutoff ->
        (n : Nat) ->
        cutoff <=N n ->
        (i : Nat) ->
        i <=N (n + suc (suc zero)) ->
        StrictLess reals
          (zeroR reals)
          (polynomialFamily n epsilon
            i
            ((n + suc (suc zero)) - i)))

putnam-1971-a4 : Set1
putnam-1971-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  PolynomialDefinitions.proposition reals
