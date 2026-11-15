-- Statement-only formalization of miniF2F test problem amc12b_2021_p4: positive natural
-- numbers in ratio 3/4 and their 84-and-70 weighted average. This file contains no proof.

module amc12b-2021-p4 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _<_)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RealField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

divide : {R : Set} → RealField R → R → R → R
divide reals x y =
  RealField.multiply reals x (RealField.inverse reals y)

Positive : Nat → Set
Positive n = (zero < n) ≡ true

amc12b-2021-p4 : Set₁
amc12b-2021-p4 =
  (R : Set) →
  (reals : RealField R) →
  (m a : Nat) →
  Positive m →
  Positive a →
  divide reals
    (RealField.fromNat reals m)
    (RealField.fromNat reals a)
    ≡
    divide reals
      (RealField.fromNat reals 3)
      (RealField.fromNat reals 4) →
  divide reals
    (RealField.add reals
      (RealField.multiply reals
        (RealField.fromNat reals 84)
        (RealField.fromNat reals m))
      (RealField.multiply reals
        (RealField.fromNat reals 70)
        (RealField.fromNat reals a)))
    (RealField.add reals
      (RealField.fromNat reals m)
      (RealField.fromNat reals a))
    ≡ RealField.fromNat reals 76
