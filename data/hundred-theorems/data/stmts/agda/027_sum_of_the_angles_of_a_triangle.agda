-- Statement-only formalization of "Sum of the Angles of a Triangle" from Hundred Theorems
-- item 027. In a real inner-product space with the standard radian angle, the three
-- angles of a triangle whose vertices are not all equal add to pi. This file contains
-- no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

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
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR
    inverse-zero :
      inverse zeroR ≡ zeroR

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
      (n : Nat) →
      fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) →
      fromNat m ≡ fromNat n →
      m ≡ n

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

subtractR :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtractR reals x y =
  CompleteOrderedField.add reals x
    (CompleteOrderedField.negate reals y)

divideR :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
divideR reals x y =
  CompleteOrderedField.multiply reals x
    (CompleteOrderedField.inverse reals y)

StrictLess :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  CompleteOrderedField.lessOrEqual reals x y ∧ x ≠ y

differenceQuotient :
  {R : Set} →
  (reals : CompleteOrderedField R) →
  (R → R) →
  R →
  R →
  R
differenceQuotient reals f x y =
  divideR reals
    (subtractR reals (f y) (f x))
    (subtractR reals y x)

DerivativeAt :
  {R : Set} →
  (reals : CompleteOrderedField R) →
  (R → R) →
  R →
  R →
  Set
DerivativeAt {R} reals f x derivative =
  (epsilon : R) →
  StrictLess reals (CompleteOrderedField.zeroR reals) epsilon →
  Exists R
    (λ delta →
      StrictLess reals (CompleteOrderedField.zeroR reals) delta ∧
      ((y : R) →
        StrictLess reals (subtractR reals x delta) y →
        StrictLess reals y (CompleteOrderedField.add reals x delta) →
        y ≠ x →
        StrictLess reals
          (subtractR reals derivative epsilon)
          (differenceQuotient reals f x y) ∧
        StrictLess reals
          (differenceQuotient reals f x y)
          (CompleteOrderedField.add reals derivative epsilon)))

record RealInnerProductAngleSpace
  {R : Set}
  (reals : CompleteOrderedField R)
  (V : Set) : Set₁ where

  open CompleteOrderedField reals

  field
    zeroV : V
    addV : V → V → V
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

    norm : V → R
    norm-nonnegative :
      (v : V) → lessOrEqual zeroR (norm v)
    norm-square :
      (v : V) → multiply (norm v) (norm v) ≡ inner v v
    norm-zero :
      (v : V) → norm v ≡ zeroR → v ≡ zeroV
    norm-negate :
      (v : V) → norm (negateV v) ≡ norm v

    pi halfPi : R
    sine cosine : R → R
    vectorAngle : V → V → R

    pi-positive :
      StrictLess reals zeroR pi
    pi-lower-bound :
      StrictLess reals (fromNat 3) pi
    pi-upper-bound :
      StrictLess reals pi (fromNat 4)
    half-pi-doubles :
      add halfPi halfPi ≡ pi

    sine-zero :
      sine zeroR ≡ zeroR
    sine-half-pi :
      sine halfPi ≡ oneR
    sine-pi :
      sine pi ≡ zeroR
    cosine-zero :
      cosine zeroR ≡ oneR
    cosine-half-pi :
      cosine halfPi ≡ zeroR
    cosine-pi :
      cosine pi ≡ negate oneR

    sine-addition :
      (x y : R) →
      sine (add x y) ≡
      add
        (multiply (sine x) (cosine y))
        (multiply (cosine x) (sine y))
    cosine-addition :
      (x y : R) →
      cosine (add x y) ≡
      add
        (multiply (cosine x) (cosine y))
        (negate (multiply (sine x) (sine y)))
    sine-negate :
      (x : R) →
      sine (negate x) ≡ negate (sine x)
    cosine-negate :
      (x : R) →
      cosine (negate x) ≡ cosine x
    trigonometric-circle :
      (x : R) →
      add
        (multiply (sine x) (sine x))
        (multiply (cosine x) (cosine x))
      ≡ oneR

    sine-at-least-negative-one :
      (x : R) →
      lessOrEqual (negate oneR) (sine x)
    sine-at-most-one :
      (x : R) →
      lessOrEqual (sine x) oneR
    cosine-at-least-negative-one :
      (x : R) →
      lessOrEqual (negate oneR) (cosine x)
    cosine-at-most-one :
      (x : R) →
      lessOrEqual (cosine x) oneR
    sine-positive-before-pi :
      (x : R) →
      StrictLess reals zeroR x →
      StrictLess reals x pi →
      StrictLess reals zeroR (sine x)

    sine-derivative-at-zero :
      DerivativeAt reals sine zeroR oneR
    sine-two-pi-periodic :
      (x : R) →
      sine (add x (add pi pi)) ≡ sine x
    cosine-two-pi-periodic :
      (x : R) →
      cosine (add x (add pi pi)) ≡ cosine x

    vector-angle-symmetric :
      (u v : V) → vectorAngle u v ≡ vectorAngle v u
    vector-angle-zero-left :
      (v : V) → vectorAngle zeroV v ≡ halfPi
    vector-angle-zero-right :
      (v : V) → vectorAngle v zeroV ≡ halfPi
    vector-angle-self :
      (v : V) → v ≠ zeroV → vectorAngle v v ≡ zeroR
    vector-angle-nonnegative :
      (u v : V) → lessOrEqual zeroR (vectorAngle u v)
    vector-angle-at-most-pi :
      (u v : V) → lessOrEqual (vectorAngle u v) pi
    vector-angle-cosine :
      (u v : V) →
      inner u v ≡
      multiply
        (multiply (norm u) (norm v))
        (cosine (vectorAngle u v))
    cosine-injective-on-angle-range :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual x pi →
      lessOrEqual zeroR y →
      lessOrEqual y pi →
      cosine x ≡ cosine y →
      x ≡ y

open CompleteOrderedField
open RealInnerProductAngleSpace

subtractV :
  {R V : Set} →
  {reals : CompleteOrderedField R} →
  RealInnerProductAngleSpace reals V →
  V →
  V →
  V
subtractV space u v =
  addV space u (negateV space v)

angleAt :
  {R V : Set} →
  {reals : CompleteOrderedField R} →
  RealInnerProductAngleSpace reals V →
  V →
  V →
  V →
  R
angleAt space a b c =
  vectorAngle space
    (subtractV space a b)
    (subtractV space c b)

module TriangleAngleSumStatement
  {R V : Set}
  (reals : CompleteOrderedField R)
  (space : RealInnerProductAngleSpace reals V) where

  proposition : Set
  proposition =
    (a b c : V) →
    Not ((a ≡ b) ∧ ((b ≡ c) ∧ (a ≡ c))) →
    add reals
      (add reals
        (angleAt space b a c)
        (angleAt space a b c))
      (angleAt space b c a)
    ≡ pi space

sum-of-the-angles-of-a-triangle : Set₁
sum-of-the-angles-of-a-triangle =
  (R V : Set) →
  (reals : CompleteOrderedField R) →
  (space : RealInnerProductAngleSpace reals V) →
  TriangleAngleSumStatement.proposition reals space
