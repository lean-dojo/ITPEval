-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_b5:
-- the real quartic 4x^4 - 4x^2 + 1 maps [-1, 1] into [0, 1] and maximizes
-- its x^4 coefficient among all real quartics with that property. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
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
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
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

four : Nat
four = suc (suc (suc (suc zero)))

record PolynomialUpToFour (R : Set) : Set where
  constructor coefficients
  field
    coefficient0 : R
    coefficient1 : R
    coefficient2 : R
    coefficient3 : R
    coefficient4 : R

open PolynomialUpToFour

evaluate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PolynomialUpToFour R ->
  R ->
  R
evaluate reals p x =
  addR reals
    (coefficient0 p)
    (multiplyR reals x
      (addR reals
        (coefficient1 p)
        (multiplyR reals x
          (addR reals
            (coefficient2 p)
            (multiplyR reals x
              (addR reals
                (coefficient3 p)
                (multiplyR reals x (coefficient4 p))))))))

InClosedInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
InClosedInterval reals lower upper x =
  lessOrEqualR reals lower x
  and
  lessOrEqualR reals x upper

QualifyingQuartic :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PolynomialUpToFour R ->
  Set
QualifyingQuartic {R} reals p =
  coefficient4 p != zeroR reals
  and
  ((x : R) ->
    InClosedInterval reals
      (negateR reals (oneR reals))
      (oneR reals)
      x ->
    InClosedInterval reals
      (zeroR reals)
      (oneR reals)
      (evaluate reals p x))

solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PolynomialUpToFour R
solution reals =
  coefficients
    (oneR reals)
    (zeroR reals)
    (negateR reals (fromNatR reals four))
    (zeroR reals)
    (fromNatR reals four)

putnam-1978-b5 : Set1
putnam-1978-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  QualifyingQuartic reals (solution reals)
  and
  ((p : PolynomialUpToFour R) ->
    QualifyingQuartic reals p ->
    lessOrEqualR reals
      (coefficient4 p)
      (coefficient4 (solution reals)))
