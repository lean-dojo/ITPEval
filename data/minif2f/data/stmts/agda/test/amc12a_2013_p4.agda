-- Statement-only formalization of miniF2F test problem amc12a_2013_p4. This file contains no
-- proof.

module amc12a-2013-p4 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RealStructure (R : Set) : Set₁ where
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

subtract : {R : Set} → RealStructure R → R → R → R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

power : {R : Set} → RealStructure R → R → Nat → R
power reals x zero = RealStructure.oneR reals
power reals x (suc n) =
  RealStructure.multiply reals x (power reals x n)

twoPower : {R : Set} → RealStructure R → Nat → R
twoPower reals n =
  power reals (RealStructure.fromNat reals 2) n

amc12a-2013-p4 : Set₁
amc12a-2013-p4 =
  (R : Set) →
  (reals : RealStructure R) →
  divide reals
    (RealStructure.add reals
      (twoPower reals 2014)
      (twoPower reals 2012))
    (subtract reals
      (twoPower reals 2014)
      (twoPower reals 2012))
  ≡
  divide reals
    (RealStructure.fromNat reals 5)
    (RealStructure.fromNat reals 3)
