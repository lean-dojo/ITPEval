-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_b6:
-- a bounded real trigonometric polynomial attaining absolute value one at
-- 2n points is constant or a phase-shifted cosine of frequency n. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {A : Set} ->
  A ->
  A ->
  Set
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where
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
oneN = suc zero

twoN : Nat
twoN = suc oneN

fourN : Nat
fourN = twoN + twoN

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
      (x y z : R) -> add (add x y) z == add x (add y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
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

maximum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ = y
... | right _ = x

absoluteValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

naturalPower :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals (naturalPower reals x n) x

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

sumThrough :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumThrough reals zero term =
  term zero
sumThrough reals (suc n) term =
  add reals
    (sumThrough reals n term)
    (term (suc n))

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

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
  naturalPower reals (negate reals (oneR reals)) n

sineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
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

leibnizTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

SineValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
SineValue reals x value =
  SeriesHasSum reals (sineTerm reals x) value

CosineValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  SeriesHasSum reals (cosineTerm reals x) value

record PiValue
  {R : Set}
  (reals : CompleteOrderedField R)
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
  (reals : CompleteOrderedField R) : Set1 where
  field
    sine cosine : R -> R
    pi : R
    sine-value :
      (x : R) -> SineValue reals x (sine x)
    cosine-value :
      (x : R) -> CosineValue reals x (cosine x)
    pi-value :
      PiValue reals pi

open StandardTrigonometry

Predicate : Set -> Set1
Predicate A =
  A -> Set

SubsetOf :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
SubsetOf {A} S T =
  (x : A) ->
  S x ->
  T x

record HasCardinality
  {A : Set}
  (S : Predicate A)
  (n : Nat) : Set where
  field
    enumerate :
      Fin n -> A
    enumerated-member :
      (i : Fin n) -> S (enumerate i)
    enumeration-complete :
      (x : A) ->
      S x ->
      Exists (Fin n) (\ i -> x == enumerate i)
    enumeration-injective :
      (i j : Fin n) ->
      enumerate i == enumerate j ->
      i == j

EqFunction :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
EqFunction {A} f g =
  (x : A) ->
  f x == g x

module Putnam1962B6Statement
  {R : Set}
  (reals : CompleteOrderedField R)
  (trigonometry : StandardTrigonometry reals) where

  twoPi : R
  twoPi =
    multiply reals
      (fromNat reals twoN)
      (pi trigonometry)

  ClosedPeriod : R -> Set
  ClosedPeriod x =
    lessOrEqual reals (zeroR reals) x
    and
    lessOrEqual reals x twoPi

  HalfOpenPeriod : R -> Set
  HalfOpenPeriod x =
    lessOrEqual reals (zeroR reals) x
    and
    StrictLess reals x twoPi

  trigonometricPolynomial :
    Nat ->
    (Nat -> R) ->
    (Nat -> R) ->
    R ->
    R
  trigonometricPolynomial n a b x =
    sumThrough reals n
      (\ k ->
        add reals
          (multiply reals
            (a k)
            (sine trigonometry
              (multiply reals (fromNat reals k) x)))
          (multiply reals
            (b k)
            (cosine trigonometry
              (multiply reals (fromNat reals k) x))))

  BoundedByOne : (R -> R) -> Set
  BoundedByOne f =
    (x : R) ->
    ClosedPeriod x ->
    lessOrEqual reals
      (absoluteValue reals (f x))
      (oneR reals)

  ExtremalOn :
    Predicate R ->
    (R -> R) ->
    Set
  ExtremalOn xs f =
    (x : R) ->
    xs x ->
    absoluteValue reals (f x) == oneR reals

  Nonconstant : (R -> R) -> Set
  Nonconstant f =
    Not
      (Exists R
        (\ constant ->
          EqFunction f (\ _ -> constant)))

  proposition : Set1
  proposition =
    (n : Nat) ->
    (a b : Nat -> R) ->
    (xs : Predicate R) ->
    (f : R -> R) ->
    EqFunction f (trigonometricPolynomial n a b) ->
    BoundedByOne f ->
    (HasCardinality xs (twoN * n)
      and
      SubsetOf xs HalfOpenPeriod) ->
    ExtremalOn xs f ->
    Nonconstant f ->
    Exists R
      (\ phase ->
        EqFunction f
          (\ x ->
            cosine trigonometry
              (add reals
                (multiply reals (fromNat reals n) x)
                phase)))

putnam-1962-b6 : Set1
putnam-1962-b6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (trigonometry : StandardTrigonometry reals) ->
  Putnam1962B6Statement.proposition reals trigonometry
