-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__081,
-- "Divergence of the Prime Reciprocal Series": the real partial sums of reciprocals
-- of prime numbers eventually exceed every real bound. This file contains no proof.

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _!=_ _<=N_

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat -> Nat -> Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

boolNot : Bool -> Bool
boolNot false = true
boolNot true = false

boolOr : Bool -> Bool -> Bool
boolOr false value = value
boolOr true _ = true

dividesBool : Nat -> Nat -> Bool
dividesBool divisor dividend =
  natEqual (naturalMod dividend divisor) zero

hasDivisorThrough : Nat -> Nat -> Bool
hasDivisorThrough n zero = false
hasDivisorThrough n (suc zero) = false
hasDivisorThrough n (suc (suc bound)) =
  boolOr
    (dividesBool (suc (suc bound)) n)
    (hasDivisorThrough n (suc bound))

isPrimeBool : Nat -> Bool
isPrimeBool zero = false
isPrimeBool (suc zero) = false
isPrimeBool (suc (suc n)) =
  boolNot (hasDivisorThrough (suc (suc n)) (suc n))

record ArchimedeanOrderedField (R : Set) : Set1 where
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

open ArchimedeanOrderedField

primeReciprocalTerm :
  {R : Set} ->
  ArchimedeanOrderedField R ->
  Nat ->
  R
primeReciprocalTerm reals n with isPrimeBool n
... | false = zeroR reals
... | true = inverse reals (fromNat reals n)

sumFirst :
  {R : Set} ->
  ArchimedeanOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  add reals
    (sumFirst reals term n)
    (term n)

primeReciprocalPartialSum :
  {R : Set} ->
  ArchimedeanOrderedField R ->
  Nat ->
  R
primeReciprocalPartialSum reals =
  sumFirst reals (primeReciprocalTerm reals)

GrowsWithoutBound :
  {R : Set} ->
  ArchimedeanOrderedField R ->
  (Nat -> R) ->
  Set
GrowsWithoutBound {R} reals sequence =
  (bound : R) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lessOrEqual reals bound (sequence n))

divergence-of-the-prime-reciprocal-series : Set1
divergence-of-the-prime-reciprocal-series =
  (R : Set) ->
  (reals : ArchimedeanOrderedField R) ->
  GrowsWithoutBound reals (primeReciprocalPartialSum reals)
