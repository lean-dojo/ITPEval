-- Statement-only formalization of miniF2F valid problem
-- algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x: the inequality
-- 2 - sqrt 2 >= 2 - x - 1 / (2 * x) for every positive real x. This file contains no proof.

module algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record RealStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
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
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
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
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

    square-root-nonnegative :
      (x : R) → lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      lessOrEqual zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : RealStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealStructure.lessOrEqual arithmetic
          x
          (RealStructure.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealStructure.lessOrEqual arithmetic x upper) →
          RealStructure.lessOrEqual arithmetic supremum upper)

record RealIsomorphism
  {C R : Set}
  (canonical : StandardReal C)
  (target : RealStructure R) : Set₁ where
  field
    to   : C → R
    from : R → C

    to-from :
      (x : R) → to (from x) ≡ x
    from-to :
      (x : C) → from (to x) ≡ x

    preserve-zero :
      to
        (RealStructure.zeroR
          (StandardReal.arithmetic canonical))
        ≡ RealStructure.zeroR target
    preserve-one :
      to
        (RealStructure.oneR
          (StandardReal.arithmetic canonical))
        ≡ RealStructure.oneR target
    preserve-add :
      (x y : C) →
      to
        (RealStructure.add
          (StandardReal.arithmetic canonical)
          x y)
        ≡ RealStructure.add target (to x) (to y)
    preserve-multiply :
      (x y : C) →
      to
        (RealStructure.multiply
          (StandardReal.arithmetic canonical)
          x y)
        ≡ RealStructure.multiply target (to x) (to y)
    preserve-negate :
      (x : C) →
      to
        (RealStructure.negate
          (StandardReal.arithmetic canonical)
          x)
        ≡ RealStructure.negate target (to x)
    preserve-inverse :
      (x : C) →
      to
        (RealStructure.inverse
          (StandardReal.arithmetic canonical)
          x)
        ≡ RealStructure.inverse target (to x)
    preserve-square-root :
      (x : C) →
      to
        (RealStructure.squareRoot
          (StandardReal.arithmetic canonical)
          x)
        ≡ RealStructure.squareRoot target (to x)
    preserve-fromNat :
      (n : Nat) →
      to
        (RealStructure.fromNat
          (StandardReal.arithmetic canonical)
          n)
        ≡ RealStructure.fromNat target n
    preserve-order :
      (x y : C) →
      RealStructure.lessOrEqual
        (StandardReal.arithmetic canonical)
        x y
      ↔
      RealStructure.lessOrEqual target (to x) (to y)

subtract : {R : Set} → RealStructure R → R → R → R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

strictlyPositive : {R : Set} → RealStructure R → R → Set
strictlyPositive reals x =
  (RealStructure.lessOrEqual reals
    (RealStructure.zeroR reals) x) ∧
  (RealStructure.zeroR reals ≠ x)

leftSide : {R : Set} → RealStructure R → R
leftSide reals =
  subtract reals
    (RealStructure.fromNat reals 2)
    (RealStructure.squareRoot reals
      (RealStructure.fromNat reals 2))

rightSide : {R : Set} → RealStructure R → R → R
rightSide reals x =
  subtract reals
    (subtract reals
      (RealStructure.fromNat reals 2)
      x)
    (divide reals
      (RealStructure.oneR reals)
      (RealStructure.multiply reals
        (RealStructure.fromNat reals 2)
        x))

algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x : Set₁
algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x =
  (C R : Set) →
  (canonical : StandardReal C) →
  (reals : RealStructure R) →
  RealIsomorphism canonical reals →
  (x : R) →
  strictlyPositive reals x →
  RealStructure.lessOrEqual reals
    (rightSide reals x)
    (leftSide reals)
