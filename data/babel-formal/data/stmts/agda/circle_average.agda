-- Statement-only formalization of the Babel-formal topic circle_average. This file contains no
-- proof.

module circle_average where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)

record AddMonoid {ℓ : Level} (R : Set ℓ) : Set ℓ where
  field
    zero      : R
    add       : R → R → R
    add-zero  : (x : R) → add x zero ≡ x
    add-comm  : (x y : R) → add x y ≡ add y x
    add-assoc : (x y z : R) → add (add x y) z ≡ add x (add y z)

record IntegralStructure {ℓ : Level} {R : Set ℓ}
                         (M : AddMonoid R) : Set ℓ where
  open AddMonoid M

  field
    integral       : (R → R) → R
    integral-ext   : (g h : R → R) →
                     ((θ : R) → g θ ≡ h θ) →
                     integral g ≡ integral h
    integral-const : (c : R) → integral (λ _ → c) ≡ c
    integral-add   : (f g : R → R) →
                     integral (λ θ → add (f θ) (g θ)) ≡
                     add (integral f) (integral g)
    integral-shift : (f : R → R) (c : R) →
                     integral (λ θ → f (add θ c)) ≡ integral f

module CircleAverage {ℓ : Level} {R : Set ℓ}
                     (M : AddMonoid R)
                     (I : IntegralStructure M) where
  open AddMonoid M
  open IntegralStructure I

  circleMap : R → R → R
  circleMap c θ = add θ c

  circleAverage : (R → R) → R → R
  circleAverage f c = integral (λ θ → f (circleMap c θ))

  circleMap-zero : Set ℓ
  circleMap-zero =
    (θ : R) → circleMap zero θ ≡ θ

  circleAverage-zero : Set ℓ
  circleAverage-zero =
    (f : R → R) → circleAverage f zero ≡ integral f

  circleAverage-add : Set ℓ
  circleAverage-add =
    (f g : R → R) (c : R) →
    circleAverage (λ z → add (f z) (g z)) c ≡
    add (circleAverage f c) (circleAverage g c)

  circleAverage-fun-add : Set ℓ
  circleAverage-fun-add =
    (f : R → R) (c : R) →
    circleAverage (λ z → f (add z c)) zero ≡ circleAverage f c

  circleMap-add : Set ℓ
  circleMap-add =
    (c d θ : R) →
    circleMap (add c d) θ ≡ circleMap c (circleMap d θ)

  circleAverage-shift : Set ℓ
  circleAverage-shift =
    (f : R → R) (c d : R) →
    circleAverage f (add c d) ≡
    circleAverage (λ z → f (add z d)) c

  circleAverage-const : Set ℓ
  circleAverage-const =
    (k c : R) → circleAverage (λ _ → k) c ≡ k

  circleAverage-add-const : Set ℓ
  circleAverage-add-const =
    (f : R → R) (k c : R) →
    circleAverage (λ z → add (f z) k) c ≡
    add (circleAverage f c) k

  circleAverage-comm-add : Set ℓ
  circleAverage-comm-add =
    (f g : R → R) (c : R) →
    circleAverage (λ z → add (f z) (g z)) c ≡
    circleAverage (λ z → add (g z) (f z)) c

  circleAverage-add-assoc : Set ℓ
  circleAverage-add-assoc =
    (f g h : R → R) (c : R) →
    circleAverage (λ z → add (add (f z) (g z)) (h z)) c ≡
    add (circleAverage f c)
        (add (circleAverage g c) (circleAverage h c))

  circleAverage-center-comm : Set ℓ
  circleAverage-center-comm =
    (f : R → R) (c d : R) →
    circleAverage f (add c d) ≡ circleAverage f (add d c)

  circleAverage-center-independent : Set ℓ
  circleAverage-center-independent =
    (f : R → R) (c : R) → circleAverage f c ≡ integral f

  circleAverage-center-eq : Set ℓ
  circleAverage-center-eq =
    (f : R → R) (c d : R) →
    circleAverage f c ≡ circleAverage f d

  circleAverage-idempotent : Set ℓ
  circleAverage-idempotent =
    (f : R → R) (c : R) →
    circleAverage (λ z → circleAverage f z) c ≡ circleAverage f c

  circleAverage-of-zero-integral : Set ℓ
  circleAverage-of-zero-integral =
    (f : R → R) (c : R) →
    integral f ≡ zero →
    circleAverage f c ≡ zero

  circleAverage-linear : Set ℓ
  circleAverage-linear =
    (f g : R → R) (c : R) →
    circleAverage (λ z → add (f z) (g z)) c ≡
    add (circleAverage f c) (circleAverage g c)

  circleAverage-shift-commute : Set ℓ
  circleAverage-shift-commute =
    (f : R → R) (c d : R) →
    circleAverage (λ z → f (circleMap d z)) c ≡
    circleAverage f (add c d)
