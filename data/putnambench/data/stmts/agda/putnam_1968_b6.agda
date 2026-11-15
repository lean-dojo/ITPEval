-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_b6:
-- no sequence of compact sets of rational numbers contains every compact set
-- of rational numbers as a subset of one of its terms. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
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

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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
      (x y : R) ->
      add x y == add y x
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
      Either (lessOrEqual x y) (lessOrEqual y x)
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
      (lessOrEqual zeroR oneR) and (zeroR != oneR)

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) ==
      add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) ==
      multiply (fromNat m) (fromNat n)
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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  (lessOrEqual reals x y) and (x != y)

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

Subset :
  Set ->
  Set1
Subset R =
  R -> Set

SubsetOf :
  {R : Set} ->
  Subset R ->
  Subset R ->
  Set
SubsetOf S T =
  (x : _) ->
  S x ->
  T x

RationalPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
RationalPoint reals x =
  Exists Int
    (\ numerator ->
      Exists Nat
        (\ denominator-minus-one ->
          x ==
          multiply reals
            (fromInt reals numerator)
            (inverse reals
              (fromNat reals
                (suc denominator-minus-one)))))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      (StrictLess reals
        (subtract reals limit epsilon)
        (sequence n))
      and
      (StrictLess reals
        (sequence n)
        (add reals limit epsilon)))

StrictlyIncreasing :
  (Nat -> Nat) ->
  Set
StrictlyIncreasing subsequence =
  (n : Nat) ->
  subsequence n <N subsequence (suc n)

Compact :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Subset R ->
  Set
Compact {R} reals S =
  (sequence : Nat -> R) ->
  ((n : Nat) -> S (sequence n)) ->
  Exists (Nat -> Nat)
    (\ subsequence ->
      (StrictlyIncreasing subsequence)
      and
      (Exists R
        (\ limit ->
          (S limit)
          and
          (ConvergesTo reals
            (\ n -> sequence (subsequence n))
            limit))))

CompactRationalSubset :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Subset R ->
  Set
CompactRationalSubset {R} reals S =
  (Compact reals S)
  and
  ((x : R) ->
    S x ->
    RationalPoint reals x)

CofinalCompactSequence :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set1
CofinalCompactSequence {R} reals =
  Exists (Nat -> Subset R)
    (\ K ->
      ((n : Nat) ->
        CompactRationalSubset reals (K n))
      and
      ((S : Subset R) ->
        CompactRationalSubset reals S ->
        Exists Nat
          (\ n -> SubsetOf S (K n))))

putnam-1968-b6 : Set1
putnam-1968-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Not (CofinalCompactSequence reals)
