-- Statement-only formalization of miniF2F test problem mathd_algebra_208: over the real
-- numbers, the square root of 1000000 minus its cube root is 900. This file contains no proof.

module mathd-algebra-208 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixr 3 _∨_
infixr 2 _∧_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record OrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessOrEqual : R → R → Set
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
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

    order-reflexive :
      (x : R) → lessOrEqual x x
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-total :
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
    add-monotone :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-or-equal-one :
      lessOrEqual zeroR oneR

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
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

power : {R : Set} → OrderedField R → R → Nat → R
power reals x zero =
  OrderedField.oneR reals
power reals x (suc n) =
  OrderedField.multiply reals x (power reals x n)

record RealRootStructure (R : Set) : Set₁ where
  field
    algebra : OrderedField R
    squareRoot cubeRoot : R → R

    square-root-nonnegative :
      (x : R) →
      OrderedField.lessOrEqual algebra
        (OrderedField.zeroR algebra)
        (squareRoot x)
    square-root-square :
      (x : R) →
      OrderedField.lessOrEqual algebra
        (OrderedField.zeroR algebra)
        x →
      OrderedField.multiply algebra
        (squareRoot x)
        (squareRoot x)
      ≡ x
    square-root-nonpositive :
      (x : R) →
      OrderedField.lessOrEqual algebra
        x
        (OrderedField.zeroR algebra) →
      squareRoot x ≡ OrderedField.zeroR algebra
    square-root-unique :
      (x y : R) →
      OrderedField.lessOrEqual algebra
        (OrderedField.zeroR algebra)
        y →
      OrderedField.multiply algebra y y ≡ x →
      squareRoot x ≡ y

    cube-root-cube :
      (x : R) →
      power algebra (cubeRoot x) 3 ≡ x
    cube-root-unique :
      (x y : R) →
      power algebra y 3 ≡ x →
      cubeRoot x ≡ y

-- Complete Archimedean ordered fields characterize the standard real-number
-- domain; the root laws select the usual square and cube roots there.
record StandardRealRoots (R : Set) : Set₁ where
  field
    roots : RealRootStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        OrderedField.lessOrEqual
          (RealRootStructure.algebra roots)
          x
          (OrderedField.fromNat
            (RealRootStructure.algebra roots)
            n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          OrderedField.lessOrEqual
            (RealRootStructure.algebra roots)
            x
            upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          OrderedField.lessOrEqual
            (RealRootStructure.algebra roots)
            x
            supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            OrderedField.lessOrEqual
              (RealRootStructure.algebra roots)
              x
              upper) →
          OrderedField.lessOrEqual
            (RealRootStructure.algebra roots)
            supremum
            upper)

subtract : {R : Set} → OrderedField R → R → R → R
subtract reals x y =
  OrderedField.add reals x (OrderedField.negate reals y)

rootDifference :
  {R : Set} →
  RealRootStructure R →
  Nat →
  R
rootDifference reals n =
  subtract algebra
    (RealRootStructure.squareRoot reals
      (OrderedField.fromNat algebra n))
    (RealRootStructure.cubeRoot reals
      (OrderedField.fromNat algebra n))
  where
    algebra = RealRootStructure.algebra reals

mathd-algebra-208 : Set₁
mathd-algebra-208 =
  (R : Set) →
  (standard : StandardRealRoots R) →
  rootDifference
    (StandardRealRoots.roots standard)
    1000000
  ≡
    OrderedField.fromNat
      (RealRootStructure.algebra
        (StandardRealRoots.roots standard))
      900
