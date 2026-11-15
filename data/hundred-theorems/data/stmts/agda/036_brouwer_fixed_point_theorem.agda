-- Statement-only formalization of "Brouwer Fixed Point Theorem" from Hundred Theorems item 036.
-- This file contains no proof.

-- Hundred Theorems item 036, "Brouwer Fixed Point Theorem": every continuous
-- self-map of a nonempty compact convex subset of a finite-dimensional real
-- Euclidean space has a fixed point. This is a statement-only formalization
-- and contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data NatLessOrEqual : Nat -> Nat -> Set where
  zero-less-or-equal :
    {n : Nat} ->
    NatLessOrEqual zero n
  successors-less-or-equal :
    {m n : Nat} ->
    NatLessOrEqual m n ->
    NatLessOrEqual (suc m) (suc n)

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  NatLessOrEqual (suc m) n

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
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

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
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  Both
    (StrictLess reals (subtract reals center radius) x)
    (StrictLess reals x (add reals center radius))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector : Set -> Nat -> Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) -> x i == y i

Region : Set -> Nat -> Set1
Region R n =
  Vector R n -> Set

addVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
addVector reals x y i =
  add reals (x i) (y i)

scaleVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n
scaleVector reals scalar x i =
  multiply reals scalar (x i)

linearCombination :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n ->
  Vector R n
linearCombination reals t x y =
  addVector reals
    (scaleVector reals t x)
    (scaleVector reals
      (subtract reals (oneR reals) t)
      y)

VectorClose :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  R ->
  Vector R n ->
  Set
VectorClose {n = n} reals center radius x =
  (i : Fin n) ->
  CloseTo reals (center i) radius (x i)

VectorConvergesTo :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  (Nat -> Vector R n) ->
  Vector R n ->
  Set
VectorConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (k : Nat) ->
      NatLessOrEqual cutoff k ->
      VectorClose reals limit epsilon (sequence k))

StrictlyIncreasing : (Nat -> Nat) -> Set
StrictlyIncreasing subsequence =
  (k : Nat) ->
  NatStrictLess (subsequence k) (subsequence (suc k))

Compact :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Region R n ->
  Set
Compact {R} {n} reals body =
  (sequence : Nat -> Vector R n) ->
  ((k : Nat) -> body (sequence k)) ->
  Exists (Nat -> Nat)
    (\ subsequence ->
      Both
        (StrictlyIncreasing subsequence)
        (Exists (Vector R n)
          (\ limit ->
            Both
              (body limit)
              (VectorConvergesTo reals
                (\ k -> sequence (subsequence k))
                limit))))

Convex :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Region R n ->
  Set
Convex {R} {n} reals body =
  (x y : Vector R n) ->
  body x ->
  body y ->
  (t : R) ->
  lessOrEqual reals (zeroR reals) t ->
  lessOrEqual reals t (oneR reals) ->
  body (linearCombination reals t x y)

ContinuousOn :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Region R n ->
  (Vector R n -> Vector R n) ->
  Set
ContinuousOn {R} {n} reals body f =
  (x : Vector R n) ->
  body x ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : Vector R n) ->
          body y ->
          VectorClose reals x delta y ->
          VectorClose reals (f x) epsilon (f y)))

Nonempty :
  {R : Set} ->
  {n : Nat} ->
  Region R n ->
  Set
Nonempty {R} {n} body =
  Exists (Vector R n) body

MapsInto :
  {R : Set} ->
  {n : Nat} ->
  Region R n ->
  (Vector R n -> Vector R n) ->
  Set
MapsInto {R} {n} body f =
  (x : Vector R n) ->
  body x ->
  body (f x)

brouwer-fixed-point-theorem : Set1
brouwer-fixed-point-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (n : Nat) ->
  (body : Region R n) ->
  (f : Vector R n -> Vector R n) ->
  Compact reals body ->
  Convex reals body ->
  Nonempty body ->
  ContinuousOn reals body f ->
  MapsInto body f ->
  Exists (Vector R n)
    (\ x ->
      Both
        (body x)
        (VectorEqual (f x) x))
