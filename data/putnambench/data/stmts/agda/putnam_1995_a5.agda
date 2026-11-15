-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_a5
-- (putnambench__agda__putnam_1995_a5): linear dependence of real solutions
-- of positive-coefficient linear ODE systems that converge to zero. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Truth : Set where
  constructor truth

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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<N_ : Nat -> Nat -> Set where
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

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
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

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
DerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative epsilon
          (differenceQuotient reals function point x)))

TendsToZeroAtPositiveInfinity :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
TendsToZeroAtPositiveInfinity {R} reals function =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ cutoff ->
      (t : R) ->
      lessOrEqual reals cutoff t ->
      CloseTo reals
        (zeroR reals)
        epsilon
        (function t))

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} terms =
  zeroR reals
sumFin reals {suc n} terms =
  add reals
    (terms fzero)
    (sumFin reals (\ i -> terms (fsuc i)))

PositiveCoefficients :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> Fin n -> R) ->
  Set
PositiveCoefficients {R} reals {n} coefficients =
  (i j : Fin n) ->
  StrictLess reals
    (zeroR reals)
    (coefficients i j)

SatisfiesDifferentialSystem :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> R -> R) ->
  (Fin n -> Fin n -> R) ->
  Set
SatisfiesDifferentialSystem {R} reals {n} functions coefficients =
  (i : Fin n) ->
  (t : R) ->
  DerivativeAt reals
    (functions i)
    t
    (sumFin reals
      (\ j ->
        multiply reals
          (coefficients i j)
          (functions j t)))

AllFunctionsTendToZero :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> R -> R) ->
  Set
AllFunctionsTendToZero reals {n} functions =
  (i : Fin n) ->
  TendsToZeroAtPositiveInfinity reals (functions i)

LinearlyIndependent :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> R -> R) ->
  Set
LinearlyIndependent {R} reals {n} functions =
  (coefficients : Fin n -> R) ->
  ((t : R) ->
    sumFin reals
      (\ i ->
        multiply reals
          (coefficients i)
          (functions i t))
    == zeroR reals) ->
  (i : Fin n) ->
  coefficients i == zeroR reals

EveryAdmissibleSystemIsDependent :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set
EveryAdmissibleSystemIsDependent {R} reals =
  (n : Nat) ->
  (functions : Fin n -> R -> R) ->
  (coefficients : Fin n -> Fin n -> R) ->
  zero <N n ->
  PositiveCoefficients reals coefficients ->
  SatisfiesDifferentialSystem reals functions coefficients ->
  AllFunctionsTendToZero reals functions ->
  Not (LinearlyIndependent reals functions)

putnam-1995-a5-solution : Set
putnam-1995-a5-solution =
  Truth

putnam-1995-a5 : Set1
putnam-1995-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Iff
    putnam-1995-a5-solution
    (EveryAdmissibleSystemIsDependent reals)
