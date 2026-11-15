-- Statement-only formalization of the Babel-formal artifact integral_comp_neg_Iic:
-- abstract ordered-field integral identities and negated interval preimages.
-- This file contains no proof.

module integral_comp_neg_Iic where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

data ⊥ {ℓ : Level} : Set ℓ where

Not : ∀ {ℓ} → Set ℓ → Set ℓ
Not {ℓ} A = A → ⊥ {ℓ}

record _∧_ {p q : Level} (A : Set p) (B : Set q) : Set (p ⊔ q) where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ {p q : Level} (A : Set p) (B : Set q) : Set (p ⊔ q) where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

record _↔_ {p q : Level} (A : Set p) (B : Set q) : Set (p ⊔ q) where
  field
    forward  : A → B
    backward : B → A

record RField {ℓ : Level} (R : Set ℓ) : Set (lsuc ℓ) where
  field
    zero : R
    one  : R
    add  : R → R → R
    opp  : R → R
    mul  : R → R → R
    le   : R → R → Set ℓ
    lt   : R → R → Set ℓ
    abs  : R → R

    add-comm         : (x y : R) → add x y ≡ add y x
    add-assoc        : (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero         : (x : R) → add x zero ≡ x
    add-opp          : (x : R) → add (opp x) x ≡ zero
    add-right-cancel : (x y z : R) → add x z ≡ add y z → x ≡ y

    mul-comm       : (x y : R) → mul x y ≡ mul y x
    mul-assoc      : (x y z : R) → mul (mul x y) z ≡ mul x (mul y z)
    mul-one        : (x : R) → mul x one ≡ x
    dist-l         : (x y z : R) →
                     mul x (add y z) ≡ add (mul x y) (mul x z)
    opp-involutive : (x : R) → opp (opp x) ≡ x

    add-le-compat : (x y z : R) → le x y → le (add x z) (add y z)
    mul-le-compat : (x y z : R) → le zero z → le x y →
                    le (mul x z) (mul y z)
    zero-le-one   : le zero one
    le-total      : (x y : R) → le x y ∨ le y x
    le-dec        : (x y : R) → le x y ∨ Not (le x y)

    le-opp      : (x y : R) → le x y → le (opp y) (opp x)
    le-antisymm : (x y : R) → le x y → le y x → x ≡ y
    lt-opp      : (x y : R) → lt x y → lt (opp y) (opp x)
    le-refl     : (x : R) → le x x
    le-trans    : (x y z : R) → le x y → le y z → le x z
    lt-def      : (x y : R) → lt x y ↔ (le x y ∧ Not (x ≡ y))

    abs-pos      : (x : R) → le zero x → abs x ≡ x
    abs-neg      : (x : R) → le x zero → abs x ≡ opp x
    abs-nonneg   : (x : R) → le zero (abs x)
    abs-opp      : (x : R) → abs (opp x) ≡ abs x
    abs-triangle : (x y : R) →
                   le (abs (add x y)) (add (abs x) (abs y))

record Integral {ℓ : Level} {R : Set ℓ}
                (RF : RField R) : Set (lsuc ℓ) where
  open RField RF

  field
    sigma : (R → Set ℓ) → (R → R) → R

    sigma-mul-const : (D : R → Set ℓ) (f : R → R) (c : R) →
      sigma D (λ x → mul c (f x)) ≡ mul c (sigma D f)
    sigma-congr : (D : R → Set ℓ) (f g : R → R) →
      ((x : R) → D x → f x ≡ g x) →
      sigma D f ≡ sigma D g
    sigma-zero : (D : R → Set ℓ) →
      sigma D (λ _ → zero) ≡ zero
    sigma-add : (D : R → Set ℓ) (f g : R → R) →
      sigma D (λ x → add (f x) (g x)) ≡
      add (sigma D f) (sigma D g)

    sigma-union-disjoint :
      (D E : R → Set ℓ) (f : R → R) →
      ((x : R) → D x → E x → ⊥ {ℓ}) →
      sigma (λ x → D x ∨ E x) f ≡
      add (sigma D f) (sigma E f)
    sigma-le : (D : R → Set ℓ) (f g : R → R) →
      ((x : R) → D x → le (f x) (g x)) →
      le (sigma D f) (sigma D g)
    sigma-dom-congr : (D E : R → Set ℓ) (f : R → R) →
      ((x : R) → D x ↔ E x) →
      sigma D f ≡ sigma E f

module PredicateStatements {ℓ : Level} {R : Set ℓ} where
  union : (R → Set ℓ) → (R → Set ℓ) → R → Set ℓ
  union D E x = D x ∨ E x

  inter : (R → Set ℓ) → (R → Set ℓ) → R → Set ℓ
  inter D E x = D x ∧ E x

  preimage : (R → R) → (R → Set ℓ) → R → Set ℓ
  preimage g D x = D (g x)

  preimage-union : Set (lsuc ℓ)
  preimage-union =
    (D E : R → Set ℓ) (g : R → R) (x : R) →
    preimage g (union D E) x ↔
    (preimage g D x ∨ preimage g E x)

  preimage-inter : Set (lsuc ℓ)
  preimage-inter =
    (D E : R → Set ℓ) (g : R → R) (x : R) →
    preimage g (inter D E) x ↔
    (preimage g D x ∧ preimage g E x)

  preimage-comp : Set (lsuc ℓ)
  preimage-comp =
    (D : R → Set ℓ) (g h : R → R) (x : R) →
    preimage g (preimage h D) x ↔
    preimage (λ y → h (g y)) D x

module OrderedStatements {ℓ : Level} {R : Set ℓ}
                         (RF : RField R) where
  open RField RF
  open PredicateStatements {R = R}

  Iic : R → R → Set ℓ
  Iic c x = le x c

  Ioi : R → R → Set ℓ
  Ioi c x = lt c x

  Iio : R → R → Set ℓ
  Iio c x = lt x c

  lt-irrefl : Set ℓ
  lt-irrefl =
    (x : R) → Not (lt x x)

  lt-trans-strict : Set ℓ
  lt-trans-strict =
    (x y z : R) → lt x y → lt y z → lt x z

  preimage-neg-Ioi : Set ℓ
  preimage-neg-Ioi =
    (c x : R) →
    preimage opp (Ioi c) x ↔ lt x (opp c)

  preimage-neg-Iic : Set ℓ
  preimage-neg-Iic =
    (c x : R) →
    preimage opp (Iic c) x ↔ Iic x (opp c)

module IntegralStatements {ℓ : Level} {R : Set ℓ}
                          (RF : RField R) (I : Integral RF) where
  open RField RF
  open Integral I
  open PredicateStatements {R = R}
  open OrderedStatements RF

  integral-neg : Set (lsuc ℓ)
  integral-neg =
    (D : R → Set ℓ) (f : R → R) →
    sigma D (λ x → opp (f x)) ≡ opp (sigma D f)

  integral-sub : Set (lsuc ℓ)
  integral-sub =
    (D : R → Set ℓ) (f g : R → R) →
    sigma D (λ x → add (f x) (opp (g x))) ≡
    add (sigma D f) (opp (sigma D g))

  sigma-empty : Set ℓ
  sigma-empty =
    (f : R → R) →
    sigma (λ _ → ⊥) f ≡ zero

  sigma-bilinear : Set (lsuc ℓ)
  sigma-bilinear =
    (D : R → Set ℓ) (f g : R → R) (c d : R) →
    sigma D (λ x → add (mul c (f x)) (mul d (g x))) ≡
    add (mul c (sigma D f)) (mul d (sigma D g))

  sigma-le-monotone : Set (lsuc ℓ)
  sigma-le-monotone =
    (D : R → Set ℓ) (f g : R → R) →
    ((x : R) → D x → le (f x) (g x)) →
    le (sigma D f) (sigma D g)

  sigma-nonneg : Set (lsuc ℓ)
  sigma-nonneg =
    (D : R → Set ℓ) (f : R → R) →
    ((x : R) → D x → le zero (f x)) →
    le zero (sigma D f)

  sigma-split : Set (lsuc ℓ)
  sigma-split =
    (D P : R → Set ℓ) (f : R → R) →
    ((x : R) → D x → P x ∨ Not (P x)) →
    sigma D f ≡
    add (sigma (λ x → D x ∧ P x) f)
        (sigma (λ x → D x ∧ Not (P x)) f)

  sigma-preimage-neg-Ioi : Set ℓ
  sigma-preimage-neg-Ioi =
    (f : R → R) (c : R) →
    sigma (preimage opp (Ioi c)) f ≡
    sigma (Iio (opp c)) f

  sigma-abs-bound : Set (lsuc ℓ)
  sigma-abs-bound =
    (D : R → Set ℓ) (f : R → R) →
    le (abs (sigma D f))
       (sigma D (λ x → abs (f x)))
