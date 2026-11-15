-- Statement-only formalization of miniF2F test problem amc12a_2021_p25. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module amc12a-2021-p25 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

AtMost : {A : Set} → (A → A → Set) → A → A → Set
AtMost relation x y = relation x y ∨ x ≡ y

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} → NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

divisorCountAux : Nat → Nat → Nat
divisorCountAux n zero = zero
divisorCountAux n (suc bound)
  with natEqual (naturalMod n (suc bound)) zero
... | true = suc (divisorCountAux n bound)
... | false = divisorCountAux n bound

divisorCount : Nat → Nat
divisorCount n = divisorCountAux n n

sumDigitsAux : Nat → Nat → Nat
sumDigitsAux zero n = zero
sumDigitsAux (suc fuel) zero = zero
sumDigitsAux (suc fuel) (suc n) =
  naturalMod (suc n) 10 +
  sumDigitsAux fuel (naturalDiv (suc n) 10)

sumDigits : Nat → Nat
sumDigits n = sumDigitsAux (suc n) n

-- Completeness and the Archimedean property identify this ordered field with
-- the standard real numbers used by the cube-root optimization problem.
record OrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessThan : R → R → Set
    fromNat : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

    order-irreflexive :
      (x : R) → lessThan x x → ⊥
    order-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-than-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

    archimedean :
      (x : R) →
      Exists Nat λ n →
        AtMost lessThan x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          AtMost lessThan x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          AtMost lessThan x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            AtMost lessThan x upper) →
          AtMost lessThan supremum upper)

divide : {R : Set} → OrderedField R → R → R → R
divide reals x y =
  OrderedField.multiply reals x (OrderedField.inverse reals y)

power : {R : Set} → OrderedField R → R → Nat → R
power reals x zero =
  OrderedField.oneR reals
power reals x (suc n) =
  OrderedField.multiply reals x (power reals x n)

record RealCubeRootStructure (R : Set) : Set₁ where
  field
    algebra : OrderedField R
    cubeRoot : R → R

    cube-root-cube :
      (x : R) →
      power algebra (cubeRoot x) 3 ≡ x
    cube-root-positive :
      (x : R) →
      OrderedField.lessThan algebra
        (OrderedField.zeroR algebra)
        x →
      OrderedField.lessThan algebra
        (OrderedField.zeroR algebra)
        (cubeRoot x)
    cube-root-unique :
      (x y : R) →
      power algebra y 3 ≡ x →
      cubeRoot x ≡ y

divisorRatio :
  {R : Set} →
  RealCubeRootStructure R →
  Nat →
  R
divisorRatio reals n =
  divide algebra
    (OrderedField.fromNat algebra (divisorCount n))
    (RealCubeRootStructure.cubeRoot reals
      (OrderedField.fromNat algebra n))
  where
    algebra = RealCubeRootStructure.algebra reals

amc12a-2021-p25 : Set₁
amc12a-2021-p25 =
  (R : Set) →
  (reals : RealCubeRootStructure R) →
  (N : Nat) →
  NatLess zero N →
  (f : Nat → R) →
  ((n : Nat) →
    NatLess zero n →
    f n ≡ divisorRatio reals n) →
  ((n : Nat) →
    n ≠ N →
    NatLess zero n →
    OrderedField.lessThan
      (RealCubeRootStructure.algebra reals)
      (f n)
      (f N)) →
  sumDigits N ≡ 9
