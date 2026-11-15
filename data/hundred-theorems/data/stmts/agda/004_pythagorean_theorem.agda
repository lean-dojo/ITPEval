-- Statement-only formalization of "Pythagorean Theorem" from Hundred Theorems item 004:
-- orthogonal vectors in a real inner-product space have additive squared norms. This file
-- contains no proof.

module pythagorean-theorem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

record CompleteOrderedField (R : Set) : Set₁ where
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
      (x y : R) →
      lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

record RealInnerProductSpace
  {R : Set}
  (reals : CompleteOrderedField R)
  (V : Set) : Set₁ where

  open CompleteOrderedField reals

  field
    zeroV : V
    addV  : V → V → V
    negateV : V → V
    scale : R → V → V

    addV-commutative :
      (u v : V) → addV u v ≡ addV v u
    addV-associative :
      (u v w : V) → addV (addV u v) w ≡ addV u (addV v w)
    addV-zero :
      (v : V) → addV v zeroV ≡ v
    addV-inverse :
      (v : V) → addV v (negateV v) ≡ zeroV

    scale-addV :
      (a : R) (u v : V) →
      scale a (addV u v) ≡ addV (scale a u) (scale a v)
    add-scale :
      (a b : R) (v : V) →
      scale (add a b) v ≡ addV (scale a v) (scale b v)
    multiply-scale :
      (a b : R) (v : V) →
      scale (multiply a b) v ≡ scale a (scale b v)
    one-scale :
      (v : V) → scale oneR v ≡ v

    inner : V → V → R
    inner-add-left :
      (u v w : V) →
      inner (addV u v) w ≡ add (inner u w) (inner v w)
    inner-scale-left :
      (a : R) (u v : V) →
      inner (scale a u) v ≡ multiply a (inner u v)
    inner-symmetric :
      (u v : V) → inner u v ≡ inner v u
    inner-nonnegative :
      (v : V) → lessOrEqual zeroR (inner v v)
    inner-definite :
      (v : V) → inner v v ≡ zeroR → v ≡ zeroV

module Statement
  {R V : Set}
  (reals : CompleteOrderedField R)
  (space : RealInnerProductSpace reals V) where

  open CompleteOrderedField reals
  open RealInnerProductSpace space

  orthogonal : V → V → Set
  orthogonal v w = inner v w ≡ zeroR

  squaredNorm : V → R
  squaredNorm v = inner v v

  proposition : Set
  proposition =
    (v w : V) →
    orthogonal v w →
    squaredNorm (addV v w) ≡
    add (squaredNorm v) (squaredNorm w)

pythagorean-theorem : Set₁
pythagorean-theorem =
  (R V : Set) →
  (reals : CompleteOrderedField R) →
  (space : RealInnerProductSpace reals V) →
  Statement.proposition reals space
