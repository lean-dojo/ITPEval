-- Statement-only formalization of thousand-theorems corpus artifact Q1816952,
-- "Schur's lemma": the endomorphism space of a simple object in a linear
-- category over an algebraically closed field has dimension one when it is
-- finite-dimensional and the category has kernels. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1816952_schur_s_lemma where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (zero to zeroN; suc to sucN)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _↔_
infixr 2 _×_

data Bottom : Set where

Not :
  {a : Level} →
  Set a →
  Set a
Not A =
  A → Bottom

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
x ≠ y =
  Not (x ≡ y)

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A → B
    backward : B → A

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (sucN n)
  fsuc  : {n : Nat} → Fin n → Fin (sucN n)

record AbelianGroup
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zero : A
    add : A → A → A
    negate : A → A
    add-associative :
      (x y z : A) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : A) →
      add x y ≡ add y x
    add-zero :
      (x : A) →
      add x zero ≡ x
    add-inverse :
      (x : A) →
      add x (negate x) ≡ zero

record Field
  {k : Level}
  (K : Set k) :
  Set k where

  field
    additive-group : AbelianGroup K
    one : K
    multiply : K → K → K
    inverse : K → K
    one-not-zero :
      one ≠ AbelianGroup.zero additive-group
    multiply-associative :
      (x y z : K) →
      multiply (multiply x y) z ≡
      multiply x (multiply y z)
    multiply-commutative :
      (x y : K) →
      multiply x y ≡ multiply y x
    multiply-one :
      (x : K) →
      multiply x one ≡ x
    inverse-zero :
      inverse (AbelianGroup.zero additive-group) ≡
      AbelianGroup.zero additive-group
    distribute :
      (x y z : K) →
      multiply x (AbelianGroup.add additive-group y z) ≡
      AbelianGroup.add additive-group
        (multiply x y)
        (multiply x z)
    multiply-inverse :
      (x : K) →
      x ≠ AbelianGroup.zero additive-group →
      multiply x (inverse x) ≡ one

evaluatePolynomial :
  {k : Level} →
  {K : Set k} →
  Field K →
  List K →
  K →
  K
evaluatePolynomial field-structure [] x =
  AbelianGroup.zero (Field.additive-group field-structure)
evaluatePolynomial field-structure (coefficient ∷ coefficients) x =
  AbelianGroup.add
    (Field.additive-group field-structure)
    coefficient
    (Field.multiply field-structure x
      (evaluatePolynomial field-structure coefficients x))

data HasNonzeroCoefficient
  {k : Level}
  {K : Set k}
  (field-structure : Field K) :
  List K →
  Set k where

  here :
    {coefficient : K} →
    {coefficients : List K} →
    coefficient ≠
      AbelianGroup.zero (Field.additive-group field-structure) →
    HasNonzeroCoefficient
      field-structure
      (coefficient ∷ coefficients)

  there :
    {coefficient : K} →
    {coefficients : List K} →
    HasNonzeroCoefficient field-structure coefficients →
    HasNonzeroCoefficient
      field-structure
      (coefficient ∷ coefficients)

data Nonconstant
  {k : Level}
  {K : Set k}
  (field-structure : Field K) :
  List K →
  Set k where

  nonconstant :
    {constant : K} →
    {higher-coefficients : List K} →
    HasNonzeroCoefficient field-structure higher-coefficients →
    Nonconstant field-structure (constant ∷ higher-coefficients)

AlgebraicallyClosed :
  {k : Level} →
  {K : Set k} →
  Field K →
  Set k
AlgebraicallyClosed field-structure =
  (coefficients : List _) →
  Nonconstant field-structure coefficients →
  Σ _
    (λ root →
      evaluatePolynomial field-structure coefficients root ≡
      AbelianGroup.zero
        (Field.additive-group field-structure))

record VectorSpace
  {k v : Level}
  {K : Set k}
  (field-structure : Field K)
  (V : Set v)
  (additive-group : AbelianGroup V) :
  Set (k ⊔ v) where

  field
    scale : K → V → V
    scale-add :
      (a : K) →
      (x y : V) →
      scale a (AbelianGroup.add additive-group x y) ≡
      AbelianGroup.add additive-group (scale a x) (scale a y)
    add-scale :
      (a b : K) →
      (x : V) →
      scale
        (AbelianGroup.add
          (Field.additive-group field-structure)
          a
          b)
        x
      ≡
      AbelianGroup.add additive-group (scale a x) (scale b x)
    multiply-scale :
      (a b : K) →
      (x : V) →
      scale (Field.multiply field-structure a b) x ≡
      scale a (scale b x)
    one-scale :
      (x : V) →
      scale (Field.one field-structure) x ≡ x

record Category
  {o h : Level}
  (Object : Set o) :
  Set (o ⊔ lsuc h) where

  infixr 7 _after_

  field
    Hom : Object → Object → Set h
    identity :
      (A : Object) →
      Hom A A
    _after_ :
      {A B C : Object} →
      Hom B C →
      Hom A B →
      Hom A C
    compose-associative :
      {A B C D : Object} →
      (f : Hom C D) →
      (g : Hom B C) →
      (h : Hom A B) →
      f after (g after h) ≡
      (f after g) after h
    identity-left :
      {A B : Object} →
      (f : Hom A B) →
      identity B after f ≡ f
    identity-right :
      {A B : Object} →
      (f : Hom A B) →
      f after identity A ≡ f

record Preadditive
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    hom-group :
      (A B : Object) →
      AbelianGroup (C.Hom A B)
    compose-add-left :
      {A B C : Object} →
      (f g : C.Hom B C) →
      (h : C.Hom A B) →
      C._after_
        (AbelianGroup.add (hom-group B C) f g)
        h
      ≡
      AbelianGroup.add
        (hom-group A C)
        (C._after_ f h)
        (C._after_ g h)
    compose-add-right :
      {A B C : Object} →
      (f : C.Hom B C) →
      (g h : C.Hom A B) →
      C._after_
        f
        (AbelianGroup.add (hom-group A B) g h)
      ≡
      AbelianGroup.add
        (hom-group A C)
        (C._after_ f g)
        (C._after_ f h)

ZeroMorphism :
  {o h : Level} →
  {Object : Set o} →
  {category : Category {o} {h} Object} →
  Preadditive category →
  (A B : Object) →
  Category.Hom category A B
ZeroMorphism preadditive A B =
  AbelianGroup.zero
    (Preadditive.hom-group preadditive A B)

record IsIso
  {o h : Level}
  {Object : Set o}
  (category : Category {o} {h} Object)
  {A B : Object}
  (arrow : Category.Hom category A B) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    inverse : C.Hom B A
    inverse-after :
      C._after_ inverse arrow ≡ C.identity A
    after-inverse :
      C._after_ arrow inverse ≡ C.identity B

Monomorphism :
  {o h : Level} →
  {Object : Set o} →
  (category : Category {o} {h} Object) →
  {A B : Object} →
  Category.Hom category A B →
  Set (o ⊔ h)
Monomorphism {Object = Object} category {A} arrow =
  (X : Object) →
  (f g : Category.Hom category X A) →
  Category._after_ category arrow f ≡
  Category._after_ category arrow g →
  f ≡ g

Simple :
  {o h : Level} →
  {Object : Set o} →
  (category : Category {o} {h} Object) →
  (preadditive : Preadditive category) →
  Object →
  Set (o ⊔ h)
Simple {Object = Object} category preadditive X =
  (Y : Object) →
  (f : Category.Hom category Y X) →
  Monomorphism category f →
  IsIso category f ↔
  (f ≠ ZeroMorphism preadditive Y X)

record IsKernel
  {o h : Level}
  {Object : Set o}
  {category : Category {o} {h} Object}
  (preadditive : Preadditive category)
  {K A B : Object}
  (kernel-arrow : Category.Hom category K A)
  (arrow : Category.Hom category A B) :
  Set (o ⊔ h) where

  private
    module C = Category category

  field
    annihilates :
      C._after_ arrow kernel-arrow ≡
      ZeroMorphism preadditive K B
    universal :
      (Y : Object) →
      (f : C.Hom Y A) →
      C._after_ arrow f ≡ ZeroMorphism preadditive Y B →
      Σ (C.Hom Y K)
        (λ lift →
          (C._after_ kernel-arrow lift ≡ f)
          ×
          ((other : C.Hom Y K) →
            C._after_ kernel-arrow other ≡ f →
            other ≡ lift))

HasKernels :
  {o h : Level} →
  {Object : Set o} →
  (category : Category {o} {h} Object) →
  (preadditive : Preadditive category) →
  Set (o ⊔ h)
HasKernels {Object = Object} category preadditive =
  {A B : Object} →
  (f : Category.Hom category A B) →
  Σ Object
    (λ K →
      Σ (Category.Hom category K A)
        (λ kernel-arrow →
          IsKernel preadditive kernel-arrow f))

record LinearCategory
  {o h k : Level}
  {Object : Set o}
  {K : Set k}
  (field-structure : Field K)
  (category : Category {o} {h} Object)
  (preadditive : Preadditive category) :
  Set (o ⊔ h ⊔ k) where

  private
    module C = Category category

  field
    hom-vector-space :
      (A B : Object) →
      VectorSpace
        field-structure
        (C.Hom A B)
        (Preadditive.hom-group preadditive A B)
    scale-after :
      {A B D : Object} →
      (scalar : K) →
      (f : C.Hom A B) →
      (g : C.Hom B D) →
      C._after_
        (VectorSpace.scale
          (hom-vector-space B D)
          scalar
          g)
        f
      ≡
      VectorSpace.scale
        (hom-vector-space A D)
        scalar
        (C._after_ g f)
    after-scale :
      {A B D : Object} →
      (scalar : K) →
      (f : C.Hom A B) →
      (g : C.Hom B D) →
      C._after_
        g
        (VectorSpace.scale
          (hom-vector-space A B)
          scalar
          f)
      ≡
      VectorSpace.scale
        (hom-vector-space A D)
        scalar
        (C._after_ g f)

sumFin :
  {v : Level} →
  {V : Set v} →
  AbelianGroup V →
  (n : Nat) →
  (Fin n → V) →
  V
sumFin group zeroN values =
  AbelianGroup.zero group
sumFin group (sucN n) values =
  AbelianGroup.add group
    (values fzero)
    (sumFin group n (λ i → values (fsuc i)))

linearCombination :
  {k v : Level} →
  {K : Set k} →
  {V : Set v} →
  (field-structure : Field K) →
  (group : AbelianGroup V) →
  (space : VectorSpace field-structure V group) →
  (n : Nat) →
  (Fin n → V) →
  (Fin n → K) →
  V
linearCombination field-structure group space n basis coefficients =
  sumFin group n
    (λ i →
      VectorSpace.scale space (coefficients i) (basis i))

record HasBasis
  {k v : Level}
  {K : Set k}
  {V : Set v}
  (field-structure : Field K)
  (group : AbelianGroup V)
  (space : VectorSpace field-structure V group)
  (dimension : Nat) :
  Set (k ⊔ v) where

  field
    basis : Fin dimension → V
    linearly-independent :
      (coefficients : Fin dimension → K) →
      linearCombination
        field-structure group space dimension basis coefficients
      ≡
      AbelianGroup.zero group →
      (i : Fin dimension) →
      coefficients i ≡
      AbelianGroup.zero
        (Field.additive-group field-structure)
    spans :
      (v : V) →
      Σ (Fin dimension → K)
        (λ coefficients →
          linearCombination
            field-structure group space dimension basis coefficients
          ≡
          v)

FiniteDimensional :
  {k v : Level} →
  {K : Set k} →
  {V : Set v} →
  (field-structure : Field K) →
  (group : AbelianGroup V) →
  VectorSpace field-structure V group →
  Set (k ⊔ v)
FiniteDimensional field-structure group space =
  Σ Nat
    (λ dimension →
      HasBasis field-structure group space dimension)

HasDimensionOne :
  {k v : Level} →
  {K : Set k} →
  {V : Set v} →
  (field-structure : Field K) →
  (group : AbelianGroup V) →
  VectorSpace field-structure V group →
  Set (k ⊔ v)
HasDimensionOne field-structure group space =
  HasBasis field-structure group space (sucN zeroN)

schur-s-lemma : Setω
schur-s-lemma =
  ∀ {o h k : Level} →
  (Object : Set o) →
  (category : Category {o} {h} Object) →
  (preadditive : Preadditive category) →
  (K : Set k) →
  (field-structure : Field K) →
  AlgebraicallyClosed field-structure →
  (linear :
    LinearCategory field-structure category preadditive) →
  HasKernels category preadditive →
  (X : Object) →
  Simple category preadditive X →
  FiniteDimensional
    field-structure
    (Preadditive.hom-group preadditive X X)
    (LinearCategory.hom-vector-space linear X X) →
  HasDimensionOne
    field-structure
    (Preadditive.hom-group preadditive X X)
    (LinearCategory.hom-vector-space linear X X)
