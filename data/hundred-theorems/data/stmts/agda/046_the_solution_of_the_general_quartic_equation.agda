-- Statement-only formalization of "The Solution of the General Quartic Equation" from Hundred
-- Theorems item 046. It gives Ferrari's four-root characterizations for the nonzero and zero
-- linear-term cases of the associated depressed quartic over characteristic-zero fields.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 2 _∨_
infix 1 _↔_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Field (F : Set) : Set₁ where
  field
    zeroF oneF : F
    add multiply : F → F → F
    negate inverse : F → F
    fromNat : Nat → F

    one-not-zero :
      oneF ≠ zeroF

    add-commutative :
      (x y : F) → add x y ≡ add y x
    add-associative :
      (x y z : F) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : F) → add x zeroF ≡ x
    add-inverse :
      (x : F) → add x (negate x) ≡ zeroF

    multiply-commutative :
      (x y : F) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : F) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : F) → multiply x oneF ≡ x
    multiply-zero :
      (x : F) → multiply x zeroF ≡ zeroF
    distribute :
      (x y z : F) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroF ≡ zeroF
    multiply-inverse :
      (x : F) →
      x ≠ zeroF →
      multiply x (inverse x) ≡ oneF

    fromNat-zero :
      fromNat zero ≡ zeroF
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneF
    characteristic-zero :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

power :
  {F : Set} →
  Field F →
  F →
  Nat →
  F
power algebra x zero =
  Field.oneF algebra
power algebra x (suc n) =
  Field.multiply algebra x (power algebra x n)

subtract :
  {F : Set} →
  Field F →
  F →
  F →
  F
subtract algebra x y =
  Field.add algebra x (Field.negate algebra y)

divide :
  {F : Set} →
  Field F →
  F →
  F →
  F
divide algebra x y =
  Field.multiply algebra x (Field.inverse algebra y)

scale :
  {F : Set} →
  Field F →
  Nat →
  F →
  F
scale algebra n x =
  Field.multiply algebra (Field.fromNat algebra n) x

product3 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F
product3 algebra x y z =
  Field.multiply algebra (Field.multiply algebra x y) z

product4 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
product4 algebra x y z w =
  Field.multiply algebra (product3 algebra x y z) w

quarticValue :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F →
  F →
  F
quarticValue algebra a b c d e x =
  Field.add algebra
    (Field.add algebra
      (Field.add algebra
        (Field.add algebra
          (Field.multiply algebra a (power algebra x 4))
          (Field.multiply algebra b (power algebra x 3)))
        (Field.multiply algebra c (power algebra x 2)))
      (Field.multiply algebra d x))
    e

depressedP :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F
depressedP algebra a b c =
  divide algebra
    (subtract algebra
      (scale algebra 8 (Field.multiply algebra a c))
      (scale algebra 3 (power algebra b 2)))
    (scale algebra 8 (power algebra a 2))

depressedQNumerator :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
depressedQNumerator algebra a b c d =
  Field.add algebra
    (subtract algebra
      (power algebra b 3)
      (scale algebra 4 (product3 algebra a b c)))
    (scale algebra 8
      (Field.multiply algebra (power algebra a 2) d))

depressedQ :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
depressedQ algebra a b c d =
  divide algebra
    (depressedQNumerator algebra a b c d)
    (scale algebra 8 (power algebra a 3))

depressedR :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F →
  F
depressedR algebra a b c d e =
  divide algebra
    (subtract algebra
      (subtract algebra
        (Field.add algebra
          (scale algebra 16
            (product3 algebra a (power algebra b 2) c))
          (scale algebra 256
            (Field.multiply algebra (power algebra a 3) e)))
        (scale algebra 3 (power algebra b 4)))
      (scale algebra 64
        (product3 algebra (power algebra a 2) b d)))
    (scale algebra 256 (power algebra a 4))

resolventValue :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
resolventValue algebra p q r u =
  subtract algebra
    (Field.add algebra
      (subtract algebra
        (subtract algebra
          (power algebra u 3)
          (Field.multiply algebra p (power algebra u 2)))
        (scale algebra 4 (Field.multiply algebra r u)))
      (scale algebra 4 (Field.multiply algebra p r)))
    (power algebra q 2)

quarticOffset :
  {F : Set} →
  Field F →
  F →
  F →
  F
quarticOffset algebra a b =
  divide algebra b (scale algebra 4 a)

nonzeroRoot1 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot1 algebra a b s v =
  subtract algebra
    (divide algebra
      (subtract algebra
        (Field.negate algebra (scale algebra 2 s))
        v)
      (Field.fromNat algebra 4))
    (quarticOffset algebra a b)

nonzeroRoot2 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot2 algebra a b s v =
  subtract algebra
    (divide algebra
      (Field.add algebra
        (Field.negate algebra (scale algebra 2 s))
        v)
      (Field.fromNat algebra 4))
    (quarticOffset algebra a b)

nonzeroRoot3 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot3 algebra a b s w =
  subtract algebra
    (divide algebra
      (subtract algebra (scale algebra 2 s) w)
      (Field.fromNat algebra 4))
    (quarticOffset algebra a b)

nonzeroRoot4 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot4 algebra a b s w =
  subtract algebra
    (divide algebra
      (Field.add algebra (scale algebra 2 s) w)
      (Field.fromNat algebra 4))
    (quarticOffset algebra a b)

FourRootCases :
  {F : Set} →
  F →
  F →
  F →
  F →
  F →
  Set
FourRootCases x root1 root2 root3 root4 =
  x ≡ root1 ∨
  x ≡ root2 ∨
  x ≡ root3 ∨
  x ≡ root4

quartic-nonzero-case : Set₁
quartic-nonzero-case =
  (F : Set) →
  (algebra : Field F) →
  (a b c d e p q r u s v w x : F) →
  a ≠ Field.zeroF algebra →
  p ≡ depressedP algebra a b c →
  q ≡ depressedQ algebra a b c d →
  q ≠ Field.zeroF algebra →
  r ≡ depressedR algebra a b c d e →
  resolventValue algebra p q r u ≡ Field.zeroF algebra →
  power algebra s 2 ≡ subtract algebra u p →
  power algebra v 2 ≡
    subtract algebra
      (scale algebra 4 (power algebra s 2))
      (scale algebra 8
        (subtract algebra u (divide algebra q s))) →
  power algebra w 2 ≡
    subtract algebra
      (scale algebra 4 (power algebra s 2))
      (scale algebra 8
        (Field.add algebra u (divide algebra q s))) →
  quarticValue algebra a b c d e x ≡ Field.zeroF algebra ↔
  FourRootCases x
    (nonzeroRoot1 algebra a b s v)
    (nonzeroRoot2 algebra a b s v)
    (nonzeroRoot3 algebra a b s w)
    (nonzeroRoot4 algebra a b s w)

zeroRoot1 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F
zeroRoot1 algebra a b v =
  subtract algebra v (quarticOffset algebra a b)

zeroRoot2 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F
zeroRoot2 algebra a b v =
  subtract algebra
    (Field.negate algebra v)
    (quarticOffset algebra a b)

quartic-zero-case : Set₁
quartic-zero-case =
  (F : Set) →
  (algebra : Field F) →
  (a b c d e p r t v w x : F) →
  a ≠ Field.zeroF algebra →
  p ≡ depressedP algebra a b c →
  depressedQNumerator algebra a b c d ≡ Field.zeroF algebra →
  r ≡ depressedR algebra a b c d e →
  power algebra t 2 ≡
    subtract algebra
      (power algebra p 2)
      (scale algebra 4 r) →
  power algebra v 2 ≡
    divide algebra
      (Field.add algebra (Field.negate algebra p) t)
      (Field.fromNat algebra 2) →
  power algebra w 2 ≡
    divide algebra
      (subtract algebra (Field.negate algebra p) t)
      (Field.fromNat algebra 2) →
  quarticValue algebra a b c d e x ≡ Field.zeroF algebra ↔
  FourRootCases x
    (zeroRoot1 algebra a b v)
    (zeroRoot2 algebra a b v)
    (zeroRoot1 algebra a b w)
    (zeroRoot2 algebra a b w)

record GeneralQuarticFormula : Set₁ where
  field
    ferrari-nonzero-case :
      quartic-nonzero-case
    biquadratic-zero-case :
      quartic-zero-case

hundred-theorems-046 : Set₁
hundred-theorems-046 =
  GeneralQuarticFormula
