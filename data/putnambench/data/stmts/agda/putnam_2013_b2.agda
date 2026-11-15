-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_b2
-- (putnambench__agda__putnam_2013_b2): the maximum at zero among nonnegative
-- real cosine polynomials whose coefficients at multiples of three vanish is
-- 3, and this maximum is attained. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2013B2 where

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
  twoN + twoN

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
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

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

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (twoN * n)))
    (fromNat reals (factorial (twoN * n)))

leibnizTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

record StandardCosine
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    cosine : R -> R
    pi : R
    cosine-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)
    pi-positive :
      StrictLess reals (zeroR reals) pi
    pi-leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals pi (fromNat reals fourN))

open StandardCosine

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ quotient -> divisor * quotient == number)

sumFromOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFromOne reals zero term =
  zeroR reals
sumFromOne reals (suc n) term =
  add reals
    (sumFromOne reals n term)
    (term (suc n))

CosinePolynomial :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardCosine reals ->
  (R -> R) ->
  Set
CosinePolynomial {R} reals trigonometry function =
  Exists Nat
    (\ degree ->
      oneN <=N degree
      and
      Exists (Nat -> R)
        (\ coefficient ->
          ((n : Nat) ->
            n <=N degree ->
            Divides threeN n ->
            coefficient n == zeroR reals)
          and
          ((x : R) ->
            function x ==
            add reals
              (oneR reals)
              (sumFromOne reals degree
                (\ n ->
                  multiply reals
                    (coefficient n)
                    (cosine trigonometry
                      (multiply reals
                        (multiply reals
                          (multiply reals
                            (fromNat reals twoN)
                            (pi trigonometry))
                          (fromNat reals n))
                        x)))))
          and
          ((x : R) ->
            lessOrEqual reals
              (zeroR reals)
              (function x))))

record IsGreatestValueAtZero
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (trigonometry : StandardCosine reals)
  (greatest : R) : Set1 where

  field
    attained :
      Exists (R -> R)
        (\ function ->
          CosinePolynomial reals trigonometry function
          and
          function (zeroR reals) == greatest)

    upper-bound :
      (function : R -> R) ->
      CosinePolynomial reals trigonometry function ->
      lessOrEqual reals
        (function (zeroR reals))
        greatest

putnam-2013-b2 : Set1
putnam-2013-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (trigonometry : StandardCosine reals) ->
  IsGreatestValueAtZero reals trigonometry
    (fromNat reals threeN)
