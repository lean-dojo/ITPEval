-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_b2:
-- the asymptotic count of positive squarish integers has constants
-- alpha = 3 / 4 and beta = 4 / 3, or no positive constants exist.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2016B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

negateInt : Int -> Int
negateInt (pos n) =
  negativeNat n
negateInt (negsuc n) =
  pos (suc n)

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

absoluteValue : Int -> Nat
absoluteValue (pos n) =
  n
absoluteValue (negsuc n) =
  suc n

IsIntegerSquare : Int -> Set
IsIntegerSquare z =
  Exists Int
    (\ root -> z == squareInt root)

IsNaturalSquare : Nat -> Set
IsNaturalSquare n =
  Exists Nat
    (\ root -> n == root * root)

distanceToSquare : Int -> Int -> Nat
distanceToSquare n root =
  absoluteValue (subtractInt n (squareInt root))

Squarish : Int -> Set
Squarish n =
  IsIntegerSquare n
  or
  Exists Int
    (\ nearestRoot ->
      IsNaturalSquare (distanceToSquare n nearestRoot)
      and
      ((otherRoot : Int) ->
        distanceToSquare n nearestRoot <=N
        distanceToSquare n otherRoot))

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

InSquarishInterval : Nat -> Nat -> Set
InSquarishInterval upper n =
  oneN <=N n
  and
  n <=N upper
  and
  Squarish (pos n)

DefinesSquarishCount : (Nat -> Nat) -> Set
DefinesSquarishCount S =
  (upper : Nat) ->
  HasCardinality
    (InSquarishInterval upper)
    (S upper)

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
ExponentialValue reals x value =
  ConvergesTo reals
    (\ n -> sumFirst reals (exponentialTerm reals x) n)
    value

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

module Putnam2016B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (powers : StandardRealPowers reals) where

  threeFourths : R
  threeFourths =
    divide reals
      (fromNat reals threeN)
      (fromNat reals fourN)

  fourThirds : R
  fourThirds =
    divide reals
      (fromNat reals fourN)
      (fromNat reals threeN)

  normalizedCount :
    (Nat -> Nat) ->
    R ->
    Nat ->
    R
  normalizedCount S alpha n =
    divide reals
      (fromNat reals (S n))
      (realPower powers (fromNat reals n) alpha)

  Qualifies :
    (Nat -> Nat) ->
    R ->
    R ->
    Set
  Qualifies S alpha beta =
    Positive reals alpha
    and
    Positive reals beta
    and
    ConvergesTo reals (normalizedCount S alpha) beta

  proposition : Set
  proposition =
    (S : Nat -> Nat) ->
    DefinesSquarishCount S ->
    (((alpha beta : R) ->
      Iff
        ((alpha == threeFourths) and (beta == fourThirds))
        (Qualifies S alpha beta))
    or
    Not
      (Exists R
        (\ alpha ->
          Exists R
            (\ beta -> Qualifies S alpha beta))))

putnam-2016-b2 : Set1
putnam-2016-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (powers : StandardRealPowers reals) ->
  Putnam2016B2Statement.proposition reals powers
