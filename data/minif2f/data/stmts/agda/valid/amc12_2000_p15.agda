-- Statement-only formalization of miniF2F valid problem amc12_2000_p15: the scaled sum of the
-- finite complex fiber over 7 for f(x / 3) = x squared + x + 1. This file contains no proof.

module amc12-2000-p15 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _∈_
infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

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
      lessOrEqual zeroR oneR ∧ (oneR ≠ zeroR)

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    archimedean :
      (x : R) → Σ Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Σ R (λ x → P x) →
      Σ R (λ upper → (x : R) → P x → lessOrEqual x upper) →
      Σ R (λ supremum →
        ((x : R) → P x → lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) → P x → lessOrEqual x upper) →
          lessOrEqual supremum upper))

record Complex (R : Set) : Set where
  constructor mkComplex
  field
    real      : R
    imaginary : R

complexAdd :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (CompleteOrderedField.add reals a c)
    (CompleteOrderedField.add reals b d)

complexNegate :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (CompleteOrderedField.negate reals a)
    (CompleteOrderedField.negate reals b)

complexMultiply :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (CompleteOrderedField.add reals
      (CompleteOrderedField.multiply reals a c)
      (CompleteOrderedField.negate reals
        (CompleteOrderedField.multiply reals b d)))
    (CompleteOrderedField.add reals
      (CompleteOrderedField.multiply reals a d)
      (CompleteOrderedField.multiply reals b c))

complexInverse :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R
complexInverse {R} reals (mkComplex a b) =
  mkComplex
    (multiply a (inverse denominator))
    (negate (multiply b (inverse denominator)))
  where
    open CompleteOrderedField reals
    denominator : R
    denominator = add (multiply a a) (multiply b b)

complexDivide :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexDivide reals x y =
  complexMultiply reals x (complexInverse reals y)

complexFromNat :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (CompleteOrderedField.fromNat reals n)
    (CompleteOrderedField.zeroR reals)

sumDividedByThree :
  {R : Set} →
  CompleteOrderedField R →
  List (Complex R) →
  Complex R
sumDividedByThree reals [] =
  complexFromNat reals 0
sumDividedByThree reals (y ∷ ys) =
  complexAdd reals
    (complexDivide reals y (complexFromNat reals 3))
    (sumDividedByThree reals ys)

amc12-2000-p15 : Set₁
amc12-2000-p15 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  (f : Complex R → Complex R) →
  ((x : Complex R) →
    f (complexDivide reals x (complexFromNat reals 3))
      ≡
      complexAdd reals
        (complexAdd reals
          (complexMultiply reals x x)
          x)
        (complexFromNat reals 1)) →
  Σ (List (Complex R)) (λ solutions →
    NoDuplicates solutions ∧
    (((y : Complex R) →
      (y ∈ solutions) ↔
      (f y ≡ complexFromNat reals 7)) ∧
    (sumDividedByThree reals solutions
      ≡
      complexNegate reals
        (complexDivide reals
          (complexFromNat reals 1)
          (complexFromNat reals 9)))))
