-- Statement-only formalization of "The Solution of a Cubic" from Hundred Theorems item 037.
-- It states Cardano's three-root characterization in both coefficient cases and contains no proof.

module HundredTheorems037 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

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
    two-not-zero :
      fromNat (suc (suc zero)) ≠ zeroF
    three-not-zero :
      fromNat (suc (suc (suc zero))) ≠ zeroF

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

cubicValue :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F →
  F
cubicValue algebra a b c d x =
  Field.add algebra
    (Field.add algebra
      (Field.add algebra
        (Field.multiply algebra a (power algebra x 3))
        (Field.multiply algebra b (power algebra x 2)))
      (Field.multiply algebra c x))
    d

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
      (scale algebra 3 (Field.multiply algebra a c))
      (power algebra b 2))
    (scale algebra 9 (power algebra a 2))

depressedQNumerator :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
depressedQNumerator algebra a b c d =
  subtract algebra
    (subtract algebra
      (scale algebra 9 (product3 algebra a b c))
      (scale algebra 2 (power algebra b 3)))
    (scale algebra 27
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
    (scale algebra 54 (power algebra a 3))

cubicOffset :
  {F : Set} →
  Field F →
  F →
  F →
  F
cubicOffset algebra a b =
  divide algebra b (scale algebra 3 a)

PrimitiveCubeRoot :
  {F : Set} →
  Field F →
  F →
  Set
PrimitiveCubeRoot algebra omega =
  power algebra omega 3 ≡ Field.oneF algebra ∧
  omega ≠ Field.oneF algebra

nonzeroRoot1 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot1 algebra a b s t =
  subtract algebra
    (subtract algebra s t)
    (cubicOffset algebra a b)

nonzeroRoot2 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot2 algebra a b omega s t =
  subtract algebra
    (subtract algebra
      (Field.multiply algebra s omega)
      (Field.multiply algebra t (power algebra omega 2)))
    (cubicOffset algebra a b)

nonzeroRoot3 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F →
  F
nonzeroRoot3 algebra a b omega s t =
  subtract algebra
    (subtract algebra
      (Field.multiply algebra s (power algebra omega 2))
      (Field.multiply algebra t omega))
    (cubicOffset algebra a b)

zeroRoot1 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F
zeroRoot1 algebra a b s =
  subtract algebra s (cubicOffset algebra a b)

zeroRoot2 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
zeroRoot2 algebra a b omega s =
  subtract algebra
    (Field.multiply algebra s omega)
    (cubicOffset algebra a b)

zeroRoot3 :
  {F : Set} →
  Field F →
  F →
  F →
  F →
  F →
  F
zeroRoot3 algebra a b omega s =
  subtract algebra
    (Field.multiply algebra s (power algebra omega 2))
    (cubicOffset algebra a b)

ThreeRootCases :
  {F : Set} →
  F →
  F →
  F →
  F →
  Set
ThreeRootCases x root1 root2 root3 =
  x ≡ root1 ∨
  x ≡ root2 ∨
  x ≡ root3

cubic-nonzero-case : Set₁
cubic-nonzero-case =
  (F : Set) →
  (algebra : Field F) →
  (a b c d omega p q r s t x : F) →
  a ≠ Field.zeroF algebra →
  PrimitiveCubeRoot algebra omega →
  p ≡ depressedP algebra a b c →
  p ≠ Field.zeroF algebra →
  q ≡ depressedQ algebra a b c d →
  power algebra r 2 ≡
    Field.add algebra
      (power algebra q 2)
      (power algebra p 3) →
  power algebra s 3 ≡ Field.add algebra q r →
  Field.multiply algebra t s ≡ p →
  cubicValue algebra a b c d x ≡ Field.zeroF algebra ↔
  ThreeRootCases x
    (nonzeroRoot1 algebra a b s t)
    (nonzeroRoot2 algebra a b omega s t)
    (nonzeroRoot3 algebra a b omega s t)

cubic-zero-case : Set₁
cubic-zero-case =
  (F : Set) →
  (algebra : Field F) →
  (a b c d omega q s x : F) →
  a ≠ Field.zeroF algebra →
  PrimitiveCubeRoot algebra omega →
  subtract algebra
    (scale algebra 3 (Field.multiply algebra a c))
    (power algebra b 2)
    ≡ Field.zeroF algebra →
  q ≡ depressedQ algebra a b c d →
  power algebra s 3 ≡ scale algebra 2 q →
  cubicValue algebra a b c d x ≡ Field.zeroF algebra ↔
  ThreeRootCases x
    (zeroRoot1 algebra a b s)
    (zeroRoot2 algebra a b omega s)
    (zeroRoot3 algebra a b omega s)

record CubicFormula : Set₁ where
  field
    cardano-nonzero-case :
      cubic-nonzero-case
    cardano-zero-case :
      cubic-zero-case

hundred-theorems-037 : Set₁
hundred-theorems-037 =
  CubicFormula
