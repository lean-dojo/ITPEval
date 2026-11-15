-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_a6:
-- positive-degree complex polynomials with coefficients plus or minus one and
-- only real roots are exactly twelve explicit signed polynomials. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_ _iff_

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n = suc m <=N n

oneN : Nat
oneN = suc zero

record CompleteOrderedField (R : Set) : Set1 where
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

open CompleteOrderedField

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexNegate :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
complexNegate reals z =
  complex
    (negateR reals (realPart z))
    (negateR reals (imaginaryPart z))

complexAdd :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals z w =
  complex
    (addR reals (realPart z) (realPart w))
    (addR reals (imaginaryPart z) (imaginaryPart w))

complexMultiply :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals z w =
  complex
    (addR reals
      (multiplyR reals (realPart z) (realPart w))
      (negateR reals
        (multiplyR reals (imaginaryPart z) (imaginaryPart w))))
    (addR reals
      (multiplyR reals (realPart z) (imaginaryPart w))
      (multiplyR reals (imaginaryPart z) (realPart w)))

complexPower :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Nat ->
  Complex R
complexPower reals z zero =
  complexOne reals
complexPower reals z (suc n) =
  complexMultiply reals (complexPower reals z n) z

data Sign : Set where
  plus  : Sign
  minus : Sign

module PolynomialDefinitions
  {R : Set}
  (reals : CompleteOrderedField R) where

  Polynomial : Set
  Polynomial = List (Complex R)

  coefficient : Polynomial -> Nat -> Complex R
  coefficient [] n =
    complexZero reals
  coefficient (c ∷ coefficients) zero =
    c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  PolynomialEqual : Polynomial -> Polynomial -> Set
  PolynomialEqual p q =
    (k : Nat) -> coefficient p k == coefficient q k

  evaluateThrough :
    Polynomial ->
    Complex R ->
    Nat ->
    Complex R
  evaluateThrough p z zero =
    coefficient p zero
  evaluateThrough p z (suc n) =
    complexAdd reals
      (evaluateThrough p z n)
      (complexMultiply reals
        (coefficient p (suc n))
        (complexPower reals z (suc n)))

  HasDegree : Polynomial -> Nat -> Set
  HasDegree p n =
    coefficient p n != complexZero reals
    and
    ((k : Nat) ->
      n <N k ->
      coefficient p k == complexZero reals)

  CoefficientsAreSignsThrough : Polynomial -> Nat -> Set
  CoefficientsAreSignsThrough p n =
    (k : Nat) ->
    k <=N n ->
    coefficient p k == complexOne reals
    or
    coefficient p k == complexNegate reals (complexOne reals)

  AllRootsRealThrough : Polynomial -> Nat -> Set
  AllRootsRealThrough p n =
    (z : Complex R) ->
    evaluateThrough p z n == complexZero reals ->
    Exists R
      (\ r -> complex r (zeroR reals) == z)

  Qualifying : Polynomial -> Set
  Qualifying p =
    Exists Nat
      (\ n ->
        oneN <=N n
        and
        (HasDegree p n
        and
        (CoefficientsAreSignsThrough p n
        and
        AllRootsRealThrough p n)))

  signValue : Sign -> Complex R
  signValue plus =
    complexOne reals
  signValue minus =
    complexNegate reals (complexOne reals)

  patternPolynomial : List Sign -> Polynomial
  patternPolynomial [] =
    []
  patternPolynomial (s ∷ signs) =
    signValue s ∷ patternPolynomial signs

  ExplicitSolution : Polynomial -> Set
  ExplicitSolution p =
    PolynomialEqual p
      (patternPolynomial (minus ∷ plus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (plus ∷ minus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (plus ∷ plus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (minus ∷ minus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (minus ∷ plus ∷ plus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (plus ∷ minus ∷ minus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (minus ∷ minus ∷ plus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (plus ∷ plus ∷ minus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (minus ∷ minus ∷ plus ∷ plus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (plus ∷ plus ∷ minus ∷ minus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (plus ∷ minus ∷ minus ∷ plus ∷ []))
    or
    PolynomialEqual p
      (patternPolynomial (minus ∷ plus ∷ plus ∷ minus ∷ []))

  proposition : Set
  proposition =
    (p : Polynomial) ->
    Qualifying p iff ExplicitSolution p

putnam-1968-a6 : Set1
putnam-1968-a6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  PolynomialDefinitions.proposition reals
