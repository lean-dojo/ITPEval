-- Statement-only formalization of PutnamBench corpus artifact putnam_2000_b3
-- (putnambench__agda__putnam_2000_b3): zero counts with multiplicity for
-- successive derivatives of a finite real sine sum are nondecreasing and
-- converge to twice its top frequency. This file contains no proof.

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN + twoN

PositiveNat : Nat -> Set
PositiveNat n =
  oneN <=N n

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
divide reals x y =
  multiply reals x (inverse reals y)

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

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

sumFinNat :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFinNat {zero} terms =
  zero
sumFinNat {suc n} terms =
  terms fzero +
  sumFinNat (\ i -> terms (fsuc i))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
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
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

alternatingPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals
    (negate reals (oneR reals))
    n

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (suc (twoN * n))))
    (fromNat reals (factorial (suc (twoN * n))))

leibnizTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

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
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    sine : R -> R
    pi : R

    sine-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)
    pi-positive :
      StrictLess reals (zeroR reals) pi
    pi-leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals pi (fromNat reals fourN))

    derivative : (R -> R) -> R -> R
    derivative-correct :
      (function : R -> R) ->
      (point derivativeValue : R) ->
      DerivativeAt reals function point derivativeValue ->
      derivative function point == derivativeValue
    derivative-totalized-at-zero :
      (function : R -> R) ->
      (point : R) ->
      Not (Exists R (DerivativeAt reals function point)) ->
      derivative function point == zeroR reals

open StandardRealAnalysis

iteratedDerivative :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardRealAnalysis reals ->
  Nat ->
  (R -> R) ->
  R ->
  R
iteratedDerivative analysis zero function =
  function
iteratedDerivative analysis (suc n) function =
  derivative analysis
    (iteratedDerivative analysis n function)

trigonometricPolynomial :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealAnalysis reals ->
  Nat ->
  (Nat -> R) ->
  R ->
  R
trigonometricPolynomial reals analysis N a t =
  sumFirst reals N
    (\ offset ->
      let j = suc offset
      in
      multiply reals
        (a j)
        (sine analysis
          (multiply reals
            (multiply reals
              (fromNat reals twoN)
              (pi analysis))
            (multiply reals
              (fromNat reals j)
              t))))

UnitHalfOpen :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
UnitHalfOpen reals t =
  lessOrEqual reals (zeroR reals) t
  and
  StrictLess reals t (oneR reals)

record FiniteSupportSum
  {A : Set}
  (domain : A -> Set)
  (term : A -> Nat)
  (total : Nat) : Set where
  field
    size : Nat
    points : Fin size -> A

    points-in-domain :
      (i : Fin size) ->
      domain (points i)
    points-nonzero :
      (i : Fin size) ->
      term (points i) != zero
    points-injective :
      (i j : Fin size) ->
      points i == points j ->
      i == j
    support-complete :
      (x : A) ->
      domain x ->
      term x != zero ->
      Exists (Fin size)
        (\ i -> x == points i)
    sum-correct :
      sumFinNat
        (\ i -> term (points i))
      ==
      total

HasFiniteSupport :
  {A : Set} ->
  (A -> Set) ->
  (A -> Nat) ->
  Set
HasFiniteSupport domain term =
  Exists Nat
    (\ total ->
      FiniteSupportSum domain term total)

TotalizedUnorderedNatSum :
  {A : Set} ->
  (A -> Set) ->
  (A -> Nat) ->
  Nat ->
  Set
TotalizedUnorderedNatSum domain term total =
  FiniteSupportSum domain term total
  or
  (Not (HasFiniteSupport domain term)
  and
  total == zero)

MultiplicityCorrect :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  (analysis : StandardRealAnalysis reals) ->
  ((R -> R) -> R -> Nat) ->
  Set
MultiplicityCorrect {R} {reals} analysis mult =
  (g : R -> R) ->
  (t : R) ->
  Exists Nat
    (\ c ->
      iteratedDerivative analysis c g t !=
      zeroR reals) ->
  (iteratedDerivative analysis (mult g t) g t !=
    zeroR reals)
  and
  ((k : Nat) ->
    k <N mult g t ->
    iteratedDerivative analysis k g t ==
    zeroR reals)

MonotoneNat :
  (Nat -> Nat) ->
  Set
MonotoneNat M =
  (i j : Nat) ->
  i <=N j ->
  M i <=N M j

NatSequenceConvergesTo :
  (Nat -> Nat) ->
  Nat ->
  Set
NatSequenceConvergesTo sequence limit =
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      sequence n == limit)

putnam-2000-b3 : Set1
putnam-2000-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  (N : Nat) ->
  PositiveNat N ->
  (a : Nat -> R) ->
  a N != zeroR reals ->
  (f : R -> R) ->
  ((t : R) ->
    f t ==
    trigonometricPolynomial reals analysis N a t) ->
  (mult : (R -> R) -> R -> Nat) ->
  MultiplicityCorrect analysis mult ->
  (M : Nat -> Nat) ->
  ((k : Nat) ->
    TotalizedUnorderedNatSum
      (UnitHalfOpen reals)
      (\ t ->
        mult
          (iteratedDerivative analysis k f)
          t)
      (M k)) ->
  MonotoneNat M
  and
  NatSequenceConvergesTo M (twoN * N)
