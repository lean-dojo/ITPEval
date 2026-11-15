-- Statement-only formalization of PutnamBench corpus artifact putnam_1991_a3:
-- classification of real polynomials whose ordered roots have derivative
-- roots at every adjacent midpoint. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

lengthList : {A : Set} -> List A -> Nat
lengthList [] =
  zero
lengthList (_ ∷ values) =
  suc (lengthList values)

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

data EndsNonzero {R : Set} (zeroValue : R) : List R -> Set where
  singleton :
    {coefficient : R} ->
    coefficient != zeroValue ->
    EndsNonzero zeroValue (coefficient ∷ [])
  prepend :
    (coefficient : R) ->
    {coefficients : List R} ->
    EndsNonzero zeroValue coefficients ->
    EndsNonzero zeroValue (coefficient ∷ coefficients)

data CanonicalCoefficients {R : Set} (zeroValue : R) : List R -> Set where
  zeroPolynomial :
    CanonicalCoefficients zeroValue []
  nonzeroPolynomial :
    {coefficients : List R} ->
    EndsNonzero zeroValue coefficients ->
    CanonicalCoefficients zeroValue coefficients

record Polynomial {R : Set}
  (reals : CompleteOrderedRealField R) : Set where
  constructor polynomial
  field
    coefficients : List R
    canonical :
      CanonicalCoefficients (zeroR reals) coefficients

open Polynomial

degree :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  Polynomial reals ->
  Nat
degree p =
  predecessor (lengthList (coefficients p))

evaluateCoefficients :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List R ->
  R ->
  R
evaluateCoefficients reals [] x =
  zeroR reals
evaluateCoefficients reals (coefficient ∷ rest) x =
  add reals
    coefficient
    (multiply reals x
      (evaluateCoefficients reals rest x))

evaluatePolynomial :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  R ->
  R
evaluatePolynomial reals p x =
  evaluateCoefficients reals (coefficients p) x

derivativeFrom :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  List R ->
  List R
derivativeFrom reals index [] =
  []
derivativeFrom reals index (coefficient ∷ rest) =
  multiply reals
    (fromNat reals index)
    coefficient
  ∷
  derivativeFrom reals (suc index) rest

derivativeCoefficients :
  {R : Set} ->
  CompleteOrderedRealField R ->
  List R ->
  List R
derivativeCoefficients reals [] =
  []
derivativeCoefficients reals (_ ∷ rest) =
  derivativeFrom reals oneN rest

evaluateDerivative :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial reals ->
  R ->
  R
evaluateDerivative reals p x =
  evaluateCoefficients reals
    (derivativeCoefficients reals (coefficients p))
    x

module Putnam1991A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  midpoint : R -> R -> R
  midpoint x y =
    divide reals
      (add reals x y)
      (fromNat reals twoN)

  RootMidpointConfiguration :
    Polynomial reals ->
    Nat ->
    Set
  RootMidpointConfiguration p n =
    Exists (Nat -> R)
      (\ roots ->
        ((i : Nat) ->
          suc i <N n ->
          StrictLess reals (roots i) (roots (suc i)))
        and
        (((i : Nat) ->
          i <N n ->
          evaluatePolynomial reals p (roots i) == zeroR reals)
        and
        ((i : Nat) ->
          suc i <N n ->
          evaluateDerivative reals p
            (midpoint (roots i) (roots (suc i)))
          ==
          zeroR reals)))

  QuadraticWithDistinctRealRoots :
    Polynomial reals ->
    Set
  QuadraticWithDistinctRealRoots p =
    degree p == twoN
    and
    Exists R
      (\ root1 ->
        Exists R
          (\ root2 ->
            root1 != root2
            and
            (evaluatePolynomial reals p root1 == zeroR reals
            and
            evaluatePolynomial reals p root2 == zeroR reals)))

  proposition : Set
  proposition =
    (p : Polynomial reals) ->
    (n : Nat) ->
    n == degree p ->
    twoN <=N n ->
    RootMidpointConfiguration p n
    iff
    QuadraticWithDistinctRealRoots p

putnam-1991-a3 : Set1
putnam-1991-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1991A3Statement.proposition reals
