-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_a1:
-- for positive real a and b, the local power-series coefficients of
-- exp(a*x) * cos(b*x) have either no zero terms or infinitely many zero terms.
-- This file contains no proof.

{-# OPTIONS --safe #-}

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

record CompleteOrderedField (R : Set) : Set1 where
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
      multiply (multiply x y) z == multiply x (multiply y z)
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

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
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

naturalPower :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

alternatingPower :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals
    (negate reals (oneR reals))
    n

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

cosineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (twoN * n)))
    (fromNat reals (factorial (twoN * n)))

record StandardExponentialCosine
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    exponential cosine : R -> R
    exponential-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)
    cosine-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)

open StandardExponentialCosine

powerSeriesTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Nat ->
  R
powerSeriesTerm reals coefficients x n =
  multiply reals
    (coefficients n)
    (naturalPower reals x n)

HasLocalExpansion :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardExponentialCosine reals ->
  R ->
  R ->
  (Nat -> R) ->
  Set
HasLocalExpansion reals functions a b coefficients =
  Exists _
    (\ radius ->
      StrictLess reals (zeroR reals) radius
      and
      ((x : _) ->
        CloseTo reals (zeroR reals) radius x ->
        SeriesHasSum reals
          (powerSeriesTerm reals coefficients x)
          (multiply reals
            (exponential functions (multiply reals a x))
            (cosine functions (multiply reals b x)))))

ZeroSetEmpty :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Set
ZeroSetEmpty reals coefficients =
  (n : Nat) ->
  coefficients n != zeroR reals

FiniteZeroSet :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Set
FiniteZeroSet reals coefficients =
  Exists Nat
    (\ cardinality ->
      Exists (Fin cardinality -> Nat)
        (\ enumeration ->
          (n : Nat) ->
          coefficients n == zeroR reals ->
          Exists (Fin cardinality)
            (\ i -> enumeration i == n)))

putnam-1970-a1 : Set1
putnam-1970-a1 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (functions : StandardExponentialCosine reals) ->
  (a b : R) ->
  StrictLess reals (zeroR reals) a ->
  StrictLess reals (zeroR reals) b ->
  (coefficients : Nat -> R) ->
  HasLocalExpansion reals functions a b coefficients ->
  ZeroSetEmpty reals coefficients
  or
  Not (FiniteZeroSet reals coefficients)
