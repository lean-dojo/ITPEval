-- Statement-only formalization of miniF2F artifact amc12b_2021_p21: the sum of the positive
-- real solutions of x^(2^(sqrt 2)) = (sqrt 2)^(2^x) is at least 2 and less than 6.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module amc12b-2021-p21 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤N_ _∈_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

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

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤N_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

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

record CompleteArchimedeanOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate reciprocal absoluteValue : R → R
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
    reciprocal-zero :
      reciprocal zeroR ≡ zeroR
    multiply-reciprocal :
      (x : R) →
      x ≠ zeroR →
      multiply x (reciprocal x) ≡ oneR

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
      lessOrEqual zeroR oneR ∧ zeroR ≠ oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    absolute-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))
    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) → subset x → lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) → subset x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → subset x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

StrictLess :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  CompleteArchimedeanOrderedField.lessOrEqual reals x y ∧ x ≠ y

subtract :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R
subtract reals x y =
  CompleteArchimedeanOrderedField.add reals x
    (CompleteArchimedeanOrderedField.negate reals y)

divide :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  R →
  R
divide reals x y =
  CompleteArchimedeanOrderedField.multiply reals x
    (CompleteArchimedeanOrderedField.reciprocal reals y)

power :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  Nat →
  R
power reals x zero =
  CompleteArchimedeanOrderedField.oneR reals
power reals x (suc n) =
  CompleteArchimedeanOrderedField.multiply reals
    (power reals x n)
    x

factorial : Nat → Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  (Nat → R) →
  Nat →
  R
sumFirst reals term zero =
  CompleteArchimedeanOrderedField.zeroR reals
sumFirst reals term (suc n) =
  CompleteArchimedeanOrderedField.add reals
    (sumFirst reals term n)
    (term n)

exponentialPartialSum :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  R →
  Nat →
  R
exponentialPartialSum reals x n =
  sumFirst reals
    (λ k →
      divide reals
        (power reals x k)
        (CompleteArchimedeanOrderedField.fromNat reals
          (factorial k)))
    n

SequentialLimit :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  (Nat → R) →
  R →
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) →
  StrictLess reals
    (CompleteArchimedeanOrderedField.zeroR reals)
    epsilon →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤N n →
      StrictLess reals
        (CompleteArchimedeanOrderedField.absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

record StandardRealAnalysis (R : Set) : Set₁ where
  field
    algebra : CompleteArchimedeanOrderedField R
    squareRoot exponential logarithm : R → R

    square-root-nonnegative :
      (x : R) →
      CompleteArchimedeanOrderedField.lessOrEqual algebra
        (CompleteArchimedeanOrderedField.zeroR algebra)
        x →
      CompleteArchimedeanOrderedField.lessOrEqual algebra
        (CompleteArchimedeanOrderedField.zeroR algebra)
        (squareRoot x)
    square-root-square :
      (x : R) →
      CompleteArchimedeanOrderedField.lessOrEqual algebra
        (CompleteArchimedeanOrderedField.zeroR algebra)
        x →
      CompleteArchimedeanOrderedField.multiply algebra
        (squareRoot x)
        (squareRoot x)
      ≡ x
    square-root-nonpositive :
      (x : R) →
      CompleteArchimedeanOrderedField.lessOrEqual algebra
        x
        (CompleteArchimedeanOrderedField.zeroR algebra) →
      squareRoot x ≡ CompleteArchimedeanOrderedField.zeroR algebra

    exponential-series :
      (x : R) →
      SequentialLimit algebra
        (exponentialPartialSum algebra x)
        (exponential x)
    exponential-positive :
      (x : R) →
      StrictLess algebra
        (CompleteArchimedeanOrderedField.zeroR algebra)
        (exponential x)
    exponential-logarithm :
      (x : R) →
      StrictLess algebra
        (CompleteArchimedeanOrderedField.zeroR algebra)
        x →
      exponential (logarithm x) ≡ x
    logarithm-exponential :
      (x : R) → logarithm (exponential x) ≡ x

realPower :
  {R : Set} →
  StandardRealAnalysis R →
  R →
  R →
  R
realPower analysis base exponent =
  StandardRealAnalysis.exponential analysis
    (CompleteArchimedeanOrderedField.multiply
      (StandardRealAnalysis.algebra analysis)
      exponent
      (StandardRealAnalysis.logarithm analysis base))

sum :
  {R : Set} →
  CompleteArchimedeanOrderedField R →
  List R →
  R
sum reals [] =
  CompleteArchimedeanOrderedField.zeroR reals
sum reals (x ∷ xs) =
  CompleteArchimedeanOrderedField.add reals x (sum reals xs)

solutionProperty :
  {R : Set} →
  StandardRealAnalysis R →
  R →
  Set
solutionProperty analysis x =
  let
    reals = StandardRealAnalysis.algebra analysis
    two = CompleteArchimedeanOrderedField.fromNat reals 2
    squareRootTwo = StandardRealAnalysis.squareRoot analysis two
  in
  StrictLess reals
      (CompleteArchimedeanOrderedField.zeroR reals)
      x
    ∧
    realPower analysis x
      (realPower analysis two squareRootTwo)
    ≡
    realPower analysis squareRootTwo
      (realPower analysis two x)

module Statement {R : Set} (analysis : StandardRealAnalysis R) where
  reals : CompleteArchimedeanOrderedField R
  reals = StandardRealAnalysis.algebra analysis

  proposition : Set
  proposition =
    (solutions : List R) →
    NoDuplicates solutions →
    ((x : R) → (x ∈ solutions) ↔ solutionProperty analysis x) →
    CompleteArchimedeanOrderedField.lessOrEqual reals
        (CompleteArchimedeanOrderedField.fromNat reals 2)
        (sum reals solutions)
      ∧
      StrictLess reals
        (sum reals solutions)
        (CompleteArchimedeanOrderedField.fromNat reals 6)

amc12b-2021-p21 : Set₁
amc12b-2021-p21 =
  (R : Set) →
  (analysis : StandardRealAnalysis R) →
  Statement.proposition analysis
