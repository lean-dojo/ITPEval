-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_a4:
-- a real-coefficient polynomial in three variables satisfying a homogeneous
-- translation identity and three prescribed values determines the distance
-- from a complex zero to be (5 / 3) times sqrt 30. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

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

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

embedReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Complex R
embedReal reals x =
  complex x (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals z w =
  complex
    (add reals (realPart z) (realPart w))
    (add reals (imaginaryPart z) (imaginaryPart w))

complexNegate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexNegate reals z =
  complex
    (negate reals (realPart z))
    (negate reals (imaginaryPart z))

complexSubtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexSubtract reals z w =
  complexAdd reals z (complexNegate reals w)

complexMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals z w =
  complex
    (add reals
      (multiply reals (realPart z) (realPart w))
      (negate reals
        (multiply reals (imaginaryPart z) (imaginaryPart w))))
    (add reals
      (multiply reals (realPart z) (imaginaryPart w))
      (multiply reals (imaginaryPart z) (realPart w)))

complexPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Nat ->
  Complex R
complexPower reals z zero =
  complexOne reals
complexPower reals z (suc n) =
  complexMultiply reals (complexPower reals z n) z

complexSquaredModulus :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexSquaredModulus reals z =
  add reals
    (square reals (realPart z))
    (square reals (imaginaryPart z))

complexModulus :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexModulus reals z =
  squareRoot reals (complexSquaredModulus reals z)

sumFinComplex :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> Complex R) ->
  Complex R
sumFinComplex reals {zero} terms =
  complexZero reals
sumFinComplex reals {suc n} terms =
  complexAdd reals
    (terms fzero)
    (sumFinComplex reals (\ i -> terms (fsuc i)))

sumThroughComplex :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (bound : Nat) ->
  (Nat -> Complex R) ->
  Complex R
sumThroughComplex reals bound term =
  sumFinComplex reals {suc bound}
    (\ i -> term (finToNat i))

record Polynomial3
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set where
  field
    coefficient : Nat -> Nat -> Nat -> Complex R
    degreeBound : Nat
    coefficient-outside-bound :
      (i j k : Nat) ->
      (degreeBound <N i
        or
        (degreeBound <N j or degreeBound <N k)) ->
      coefficient i j k == complexZero reals

open Polynomial3

evaluatePolynomial3 :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial3 reals ->
  Complex R ->
  Complex R ->
  Complex R ->
  Complex R
evaluatePolynomial3 reals polynomial x y z =
  sumThroughComplex reals
    (degreeBound polynomial)
    (\ i ->
      sumThroughComplex reals
        (degreeBound polynomial)
        (\ j ->
          sumThroughComplex reals
            (degreeBound polynomial)
            (\ k ->
              complexMultiply reals
                (coefficient polynomial i j k)
                (complexMultiply reals
                  (complexPower reals x i)
                  (complexMultiply reals
                    (complexPower reals y j)
                    (complexPower reals z k))))))

RealCoefficients :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Polynomial3 reals ->
  Set
RealCoefficients reals polynomial =
  (i j k : Nat) ->
  imaginaryPart (coefficient polynomial i j k) == zeroR reals

module Putnam1987A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  oneN : Nat
  oneN =
    suc zero

  twoN : Nat
  twoN =
    suc oneN

  threeN : Nat
  threeN =
    suc twoN

  fourN : Nat
  fourN =
    suc threeN

  fiveN : Nat
  fiveN =
    suc fourN

  sixN : Nat
  sixN =
    suc fiveN

  tenN : Nat
  tenN =
    fiveN + fiveN

  thirtyN : Nat
  thirtyN =
    fiveN * sixN

  four five six ten thirty : R
  four =
    fromNat reals fourN
  five =
    fromNat reals fiveN
  six =
    fromNat reals sixN
  ten =
    fromNat reals tenN
  thirty =
    fromNat reals thirtyN

  solution : R
  solution =
    multiply reals
      (divide reals five (fromNat reals threeN))
      (squareRoot reals thirty)

  proposition : Set
  proposition =
    (P : Polynomial3 reals) ->
    RealCoefficients reals P ->
    (F : R -> R -> R) ->
    ((x y z u : R) ->
      evaluatePolynomial3 reals P
        (embedReal reals (multiply reals u x))
        (embedReal reals (multiply reals u y))
        (embedReal reals (multiply reals u z))
      ==
      embedReal reals
        (multiply reals
          (square reals u)
          (F
            (subtract reals y x)
            (subtract reals z x)))) ->
    evaluatePolynomial3 reals P
      (embedReal reals (oneR reals))
      (complexZero reals)
      (complexZero reals)
      == embedReal reals four ->
    evaluatePolynomial3 reals P
      (complexZero reals)
      (embedReal reals (oneR reals))
      (complexZero reals)
      == embedReal reals five ->
    evaluatePolynomial3 reals P
      (complexZero reals)
      (complexZero reals)
      (embedReal reals (oneR reals))
      == embedReal reals six ->
    (A B C : Complex R) ->
    evaluatePolynomial3 reals P A B C == complexZero reals ->
    complexModulus reals (complexSubtract reals B A) == ten ->
    complexModulus reals (complexSubtract reals C A) == solution

putnam-1987-a4 : Set1
putnam-1987-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1987A4Statement.proposition reals
