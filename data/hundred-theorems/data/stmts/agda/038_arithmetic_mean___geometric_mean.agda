-- Statement-only formalization of "Arithmetic Mean / Geometric Mean" from Hundred Theorems item
-- 038. This file contains no proof.

-- Statement-only formalization for hundred-theorems__agda__038:
-- "Arithmetic Mean / Geometric Mean" (Hundred Theorems item 038). Every nonempty
-- finite family of nonnegative real numbers has product at most its arithmetic
-- mean raised to the size of the family. This file contains no proof.

module ArithmeticMeanGeometricMean where

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
    first : A
    second : B

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

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
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

power :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
power reals x zero = oneR reals
power reals x (suc n) =
  multiply reals x (power reals x n)

sumFin :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} values =
  zeroR reals
sumFin reals {suc n} values =
  add reals
    (values fzero)
    (sumFin reals (\ i -> values (fsuc i)))

productFin :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
productFin reals {zero} values =
  oneR reals
productFin reals {suc n} values =
  multiply reals
    (values fzero)
    (productFin reals (\ i -> values (fsuc i)))

arithmetic-mean-geometric-mean : Set1
arithmetic-mean-geometric-mean =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (n : Nat) ->
  (values : Fin (suc n) -> R) ->
  ((i : Fin (suc n)) ->
    lessOrEqual reals (zeroR reals) (values i)) ->
  lessOrEqual reals
    (productFin reals values)
    (power reals
      (divide reals
        (sumFin reals values)
        (fromNat reals (suc n)))
      (suc n))
