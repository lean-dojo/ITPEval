-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_b5
-- (putnambench__agda__putnam_2016_b5): functions from (1,infinity) to
-- (1,infinity) satisfying the prescribed two-sided power inequalities are
-- exactly the functions x |-> x^c for a positive real c. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Putnam2016B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

record Iff (A B : Set) : Set where
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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    absoluteValueR : R -> R
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

    absolute-value-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (absoluteValueR x)
    absolute-value-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValueR x == x
    absolute-value-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValueR x == negate x

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
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

cube :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
cube reals x =
  multiply reals (multiply reals x x) x

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Positive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (absoluteValueR reals
          (subtract reals (sequence n) limit))
        epsilon)

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  add reals
    (sumFirst reals term n)
    (term n)

oneN : Nat
oneN =
  suc zero

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

exponentialTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x result =
  ConvergesTo reals
    (\ n -> sumFirst reals (exponentialTerm reals x) n)
    result

record StandardRealPowers
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential logarithm : R -> R

    exponential-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

    exponential-positive :
      (x : R) ->
      Positive reals (exponential x)

    exponential-injective :
      (x y : R) ->
      exponential x == exponential y ->
      x == y

    exponential-logarithm :
      (x : R) ->
      Positive reals x ->
      exponential (logarithm x) == x

open StandardRealPowers

realPower :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardRealPowers reals ->
  R ->
  R ->
  R
realPower {reals = reals} powers base exponent =
  exponential powers
    (multiply reals exponent (logarithm powers base))

record AboveOne
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set where
  constructor aboveOne
  field
    number : R
    number-above-one :
      StrictLess reals (oneR reals) number

open AboveOne

module Putnam2016B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (powers : StandardRealPowers reals) where

  FunctionOnAboveOne : Set
  FunctionOnAboveOne =
    AboveOne reals -> AboveOne reals

  Solution :
    FunctionOnAboveOne ->
    Set
  Solution f =
    Exists R
      (\ c ->
        Positive reals c
        and
        ((x : AboveOne reals) ->
          number (f x) ==
          realPower powers (number x) c))

  FunctionalInequality :
    FunctionOnAboveOne ->
    Set
  FunctionalInequality f =
    (x y : AboveOne reals) ->
    (lessOrEqual reals
      (square reals (number x))
      (number y)
    and
    lessOrEqual reals
      (number y)
      (cube reals (number x))) ->
    (lessOrEqual reals
      (square reals (number (f x)))
      (number (f y))
    and
    lessOrEqual reals
      (number (f y))
      (cube reals (number (f x))))

  proposition : Set
  proposition =
    (f : FunctionOnAboveOne) ->
    Iff
      (Solution f)
      (FunctionalInequality f)

putnam-2016-b5 : Set1
putnam-2016-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (powers : StandardRealPowers reals) ->
  Putnam2016B5Statement.proposition reals powers
