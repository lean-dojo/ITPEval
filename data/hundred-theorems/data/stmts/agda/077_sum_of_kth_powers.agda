-- Statement-only formalization of Hundred Theorems artifact
-- hundred-theorems__agda__077, "Sum of kth Powers": Faulhaber's formula
-- expressing an inclusive sum of natural-number powers using Bernoulli
-- numbers and Bernoulli polynomials over the real numbers. This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)
open import Agda.Builtin.Sigma using (Σ)

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

record CompleteArchimedeanOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) ->
      Σ Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set) ->
      Σ R (\ x -> P x) ->
      Σ R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Σ R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

subtractR :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  CompleteArchimedeanOrderedField.addR reals x
    (CompleteArchimedeanOrderedField.negateR reals y)

divideR :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  CompleteArchimedeanOrderedField.multiplyR reals x
    (CompleteArchimedeanOrderedField.inverseR reals y)

powerR :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  CompleteArchimedeanOrderedField.oneR reals
powerR reals x (suc n) =
  CompleteArchimedeanOrderedField.multiplyR reals
    (powerR reals x n)
    x

sumThroughR :
  {R : Set} ->
  CompleteArchimedeanOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumThroughR reals term zero =
  term zero
sumThroughR reals term (suc n) =
  CompleteArchimedeanOrderedField.addR reals
    (sumThroughR reals term n)
    (term (suc n))

choose : Nat -> Nat -> Nat
choose n zero = suc zero
choose zero (suc k) = zero
choose (suc n) (suc k) = choose n (suc k) + choose n k

sum-of-kth-powers : Set1
sum-of-kth-powers =
  (R : Set) ->
  (reals : CompleteArchimedeanOrderedField R) ->
  (bernoulli : Nat -> R) ->
  (bernpoly : Nat -> R -> R) ->
  bernoulli zero ==
    CompleteArchimedeanOrderedField.oneR reals ->
  ((r : Nat) ->
    bernoulli (suc r) ==
      divideR reals
        (CompleteArchimedeanOrderedField.negateR reals
          (sumThroughR reals
            (\ j ->
              CompleteArchimedeanOrderedField.multiplyR reals
                (CompleteArchimedeanOrderedField.fromNatR reals
                  (choose (suc (suc r)) j))
                (bernoulli j))
            r))
        (CompleteArchimedeanOrderedField.fromNatR reals
          (suc (suc r)))) ->
  ((r : Nat) ->
    (x : R) ->
    bernpoly r x ==
      sumThroughR reals
        (\ k ->
          CompleteArchimedeanOrderedField.multiplyR reals
            (CompleteArchimedeanOrderedField.multiplyR reals
              (CompleteArchimedeanOrderedField.fromNatR reals
                (choose r k))
              (bernoulli k))
            (powerR reals x (r - k)))
        r) ->
  (m n : Nat) ->
  sumThroughR reals
      (\ k ->
        powerR reals
          (CompleteArchimedeanOrderedField.fromNatR reals k)
          m)
      n
    ==
  divideR reals
    (subtractR reals
      (bernpoly (suc m)
        (CompleteArchimedeanOrderedField.addR reals
          (CompleteArchimedeanOrderedField.fromNatR reals n)
          (CompleteArchimedeanOrderedField.oneR reals)))
      (bernpoly (suc m)
        (CompleteArchimedeanOrderedField.zeroR reals)))
    (CompleteArchimedeanOrderedField.fromNatR reals (suc m))
