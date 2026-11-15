-- Statement-only formalization of miniF2F test problem aime_1983_p3: the product of all
-- real roots of a square-root radical equation is 20. This file contains no proof.

module aime-1983-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_ _∈_
infixr 5 _∷_
infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
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

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {y : A} {xs : List A} →
    x ≡ y →
    x ∈ (y ∷ xs)
  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

foldLeft : {A : Set} → (A → A → A) → A → List A → A
foldLeft operation accumulator [] = accumulator
foldLeft operation accumulator (x ∷ xs) =
  foldLeft operation (operation accumulator x) xs

record RealStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R

    one-not-zero : oneR ≠ zeroR

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

square : {R : Set} → RealStructure R → R → R
square reals x =
  RealStructure.multiply reals x x

quadratic : {R : Set} → RealStructure R → Nat → R → R
quadratic reals constant x =
  add (add (square reals x) (multiply (fromNat 18) x))
      (fromNat constant)
  where
    open RealStructure reals

formula : {R : Set} → RealStructure R → R → R
formula reals x =
  add (quadratic reals 30 x)
      (negate (multiply (fromNat 2) (squareRoot (quadratic reals 45 x))))
  where
    open RealStructure reals

aime-1983-p3 : Set₁
aime-1983-p3 =
  (C R : Set) →
  (canonical : StandardReal C) →
  (reals : RealStructure R) →
  RealIsomorphism canonical reals →
  (f : R → R) →
  ((x : R) → f x ≡ formula reals x) →
  (roots : List R) →
  ((x : R) → (x ∈ roots) ↔ (f x ≡ RealStructure.zeroR reals)) →
  NoDuplicates roots →
  foldLeft
    (RealStructure.multiply reals)
    (RealStructure.oneR reals)
    roots
    ≡ RealStructure.fromNat reals 20
