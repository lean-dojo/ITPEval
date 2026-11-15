-- Statement-only formalization of PutnamBench corpus artifact putnam_2008_a5
-- (putnambench__agda__putnam_2008_a5): real polynomial values forming the
-- counterclockwise vertices of a regular n-gon force one polynomial to have
-- degree at least n - 1. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2008A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
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

fourN : Nat
fourN =
  twoN + twoN

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

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
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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

SineValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
SineValue reals x value =
  SeriesHasSum reals
    (sineTerm reals x)
    value

CosineValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  SeriesHasSum reals
    (cosineTerm reals x)
    value

record PiValue
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (value : R) : Set where
  field
    positive :
      StrictLess reals (zeroR reals) value
    leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals value (fromNat reals fourN))

record StandardTrigonometry
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    sine cosine : R -> R
    pi : R
    sine-value :
      (x : R) ->
      SineValue reals x (sine x)
    cosine-value :
      (x : R) ->
      CosineValue reals x (cosine x)
    pi-value :
      PiValue reals pi

open StandardTrigonometry

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

complexZero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexZero reals =
  complex
    (zeroR reals)
    (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals (complex a b) (complex c d) =
  complex
    (add reals a c)
    (add reals b d)

complexMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals (complex a b) (complex c d) =
  complex
    (subtract reals
      (multiply reals a c)
      (multiply reals b d))
    (add reals
      (multiply reals a d)
      (multiply reals b c))

cis :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardTrigonometry reals ->
  R ->
  Complex R
cis trigonometry angle =
  complex
    (cosine trigonometry angle)
    (sine trigonometry angle)

Polynomial : Set -> Set
Polynomial R =
  List R

coefficient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  R
coefficient reals [] n =
  zeroR reals
coefficient reals (c ∷ coefficients) zero =
  c
coefficient reals (c ∷ coefficients) (suc n) =
  coefficient reals coefficients n

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals [] x =
  zeroR reals
evaluatePolynomial reals (c ∷ coefficients) x =
  add reals
    c
    (multiply reals
      x
      (evaluatePolynomial reals coefficients x))

DegreeAtLeast :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  Set
DegreeAtLeast reals polynomial lower =
  Exists Nat
    (\ index ->
      lower <=N index
      and
      coefficient reals polynomial index != zeroR reals)

module Putnam2008A5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (trigonometry : StandardTrigonometry reals) where

  polygonAngle : Nat -> Nat -> R
  polygonAngle n k =
    divide reals
      (multiply reals
        (multiply reals
          (fromNat reals twoN)
          (pi trigonometry))
        (fromNat reals k))
      (fromNat reals n)

  polynomialPoint :
    Polynomial R ->
    Polynomial R ->
    Nat ->
    Complex R
  polynomialPoint f g k =
    complex
      (evaluatePolynomial reals f (fromNat reals k))
      (evaluatePolynomial reals g (fromNat reals k))

  InIndexRange : Nat -> Nat -> Set
  InIndexRange n k =
    oneN <=N k and k <=N n

  FormsRegularCounterclockwisePolygon :
    Nat ->
    Polynomial R ->
    Polynomial R ->
    Set
  FormsRegularCounterclockwisePolygon n f g =
    Exists (Complex R)
      (\ center ->
        Exists (Complex R)
          (\ scale ->
            scale != complexZero reals
            and
            ((k : Nat) ->
              InIndexRange n k ->
              polynomialPoint f g k ==
              complexAdd reals center
                (complexMultiply reals scale
                  (cis trigonometry (polygonAngle n k))))))

  proposition : Set
  proposition =
    (n : Nat) ->
    suc (suc (suc zero)) <=N n ->
    (f g : Polynomial R) ->
    FormsRegularCounterclockwisePolygon n f g ->
    DegreeAtLeast reals f (predecessor n)
    or
    DegreeAtLeast reals g (predecessor n)

putnam-2008-a5 : Set1
putnam-2008-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (trigonometry : StandardTrigonometry reals) ->
  Putnam2008A5Statement.proposition reals trigonometry
