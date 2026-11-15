-- Statement-only formalization of thousand-theorems corpus artifact Q1420905,
-- "Hilbert's theorem 90": in a finite cyclic Galois field extension, every
-- element of norm one is a quotient y / g(y) for a nonzero y.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1420905HilbertsTheoremNinety where

open import Agda.Primitive using (Level; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat)
  renaming (zero to zeroN; suc to sucN)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
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

record CommutativeRing
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zero one : A
    add multiply : A → A → A
    negate : A → A

    add-associative :
      (x y z : A) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : A) →
      add x y ≡ add y x
    add-zero-left :
      (x : A) →
      add zero x ≡ x
    add-zero-right :
      (x : A) →
      add x zero ≡ x
    add-inverse-left :
      (x : A) →
      add (negate x) x ≡ zero
    add-inverse-right :
      (x : A) →
      add x (negate x) ≡ zero

    multiply-associative :
      (x y z : A) →
      multiply (multiply x y) z ≡
      multiply x (multiply y z)
    multiply-commutative :
      (x y : A) →
      multiply x y ≡ multiply y x
    multiply-one-left :
      (x : A) →
      multiply one x ≡ x
    multiply-one-right :
      (x : A) →
      multiply x one ≡ x
    multiply-zero-left :
      (x : A) →
      multiply zero x ≡ zero
    multiply-zero-right :
      (x : A) →
      multiply x zero ≡ zero

    distribute-left :
      (x y z : A) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : A) →
      multiply (add x y) z ≡
      add (multiply x z) (multiply y z)

record Field
  {a : Level}
  (A : Set a) :
  Set a where

  field
    ring : CommutativeRing A
    inverse : A → A
    one-not-zero :
      CommutativeRing.one ring ≠
      CommutativeRing.zero ring
    inverse-zero :
      inverse (CommutativeRing.zero ring) ≡
      CommutativeRing.zero ring
    inverse-left :
      (x : A) →
      x ≠ CommutativeRing.zero ring →
      CommutativeRing.multiply ring (inverse x) x ≡
      CommutativeRing.one ring
    inverse-right :
      (x : A) →
      x ≠ CommutativeRing.zero ring →
      CommutativeRing.multiply ring x (inverse x) ≡
      CommutativeRing.one ring

record RingHom
  {a b : Level}
  {A : Set a}
  {B : Set b}
  (domain : CommutativeRing A)
  (codomain : CommutativeRing B) :
  Set (a ⊔ b) where

  field
    map : A → B
    map-zero :
      map (CommutativeRing.zero domain) ≡
      CommutativeRing.zero codomain
    map-one :
      map (CommutativeRing.one domain) ≡
      CommutativeRing.one codomain
    map-add :
      (x y : A) →
      map (CommutativeRing.add domain x y) ≡
      CommutativeRing.add codomain (map x) (map y)
    map-multiply :
      (x y : A) →
      map (CommutativeRing.multiply domain x y) ≡
      CommutativeRing.multiply codomain (map x) (map y)

sumFin :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  (n : Nat) →
  (Fin n → A) →
  A
sumFin ring zeroN values =
  CommutativeRing.zero ring
sumFin ring (sucN n) values =
  CommutativeRing.add ring
    (values fzero)
    (sumFin ring n (λ i → values (fsuc i)))

productFin :
  {a : Level} →
  {A : Set a} →
  CommutativeRing A →
  (n : Nat) →
  (Fin n → A) →
  A
productFin ring zeroN values =
  CommutativeRing.one ring
productFin ring (sucN n) values =
  CommutativeRing.multiply ring
    (values fzero)
    (productFin ring n (λ i → values (fsuc i)))

linearCombination :
  {k l : Level} →
  {K : Set k} →
  {L : Set l} →
  (base : CommutativeRing K) →
  (extension : CommutativeRing L) →
  RingHom base extension →
  (n : Nat) →
  (Fin n → L) →
  (Fin n → K) →
  L
linearCombination base extension algebra-map n vectors coefficients =
  sumFin extension n
    (λ i →
      CommutativeRing.multiply extension
        (RingHom.map algebra-map (coefficients i))
        (vectors i))

record HasBasis
  {k l : Level}
  {K : Set k}
  {L : Set l}
  (base : CommutativeRing K)
  (extension : CommutativeRing L)
  (algebra-map : RingHom base extension)
  (dimension : Nat) :
  Set (k ⊔ l) where

  field
    basis : Fin dimension → L
    linearly-independent :
      (coefficients : Fin dimension → K) →
      linearCombination
        base extension algebra-map dimension basis coefficients
      ≡
      CommutativeRing.zero extension →
      (i : Fin dimension) →
      coefficients i ≡ CommutativeRing.zero base
    spans :
      (x : L) →
      Σ (Fin dimension → K)
        (λ coefficients →
          linearCombination
            base extension algebra-map dimension basis coefficients
          ≡
          x)

record KAutomorphism
  {k l : Level}
  {K : Set k}
  {L : Set l}
  (base-field : Field K)
  (extension-field : Field L)
  (algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)) :
  Set (k ⊔ l) where

  private
    base = Field.ring base-field
    extension = Field.ring extension-field

  field
    apply inverse-apply : L → L
    apply-after-inverse :
      (x : L) →
      apply (inverse-apply x) ≡ x
    inverse-after-apply :
      (x : L) →
      inverse-apply (apply x) ≡ x
    apply-zero :
      apply (CommutativeRing.zero extension) ≡
      CommutativeRing.zero extension
    apply-one :
      apply (CommutativeRing.one extension) ≡
      CommutativeRing.one extension
    apply-add :
      (x y : L) →
      apply (CommutativeRing.add extension x y) ≡
      CommutativeRing.add extension (apply x) (apply y)
    apply-multiply :
      (x y : L) →
      apply (CommutativeRing.multiply extension x y) ≡
      CommutativeRing.multiply extension (apply x) (apply y)
    fixes-base :
      (x : K) →
      apply (RingHom.map algebra-map x) ≡
      RingHom.map algebra-map x

AutomorphismEqual :
  {k l : Level} →
  {K : Set k} →
  {L : Set l} →
  {base-field : Field K} →
  {extension-field : Field L} →
  {algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)} →
  KAutomorphism base-field extension-field algebra-map →
  KAutomorphism base-field extension-field algebra-map →
  Set l
AutomorphismEqual {L = L} left right =
  (x : L) →
  KAutomorphism.apply left x ≡
  KAutomorphism.apply right x

iterate :
  {a : Level} →
  {A : Set a} →
  (A → A) →
  Nat →
  A →
  A
iterate f zeroN x =
  x
iterate f (sucN n) x =
  f (iterate f n x)

integerAction :
  {k l : Level} →
  {K : Set k} →
  {L : Set l} →
  {base-field : Field K} →
  {extension-field : Field L} →
  {algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)} →
  KAutomorphism base-field extension-field algebra-map →
  Int →
  L →
  L
integerAction g (pos n) =
  iterate (KAutomorphism.apply g) n
integerAction g (negsuc n) =
  iterate (KAutomorphism.inverse-apply g) (sucN n)

GeneratedBy :
  {k l : Level} →
  {K : Set k} →
  {L : Set l} →
  {base-field : Field K} →
  {extension-field : Field L} →
  {algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)} →
  KAutomorphism base-field extension-field algebra-map →
  KAutomorphism base-field extension-field algebra-map →
  Set l
GeneratedBy {L = L} generator automorphism =
  Σ Int
    (λ power →
      (x : L) →
      integerAction generator power x ≡
      KAutomorphism.apply automorphism x)

record FiniteGaloisExtension
  {k l : Level}
  {K : Set k}
  {L : Set l}
  (base-field : Field K)
  (extension-field : Field L)
  (algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)) :
  Set (k ⊔ l) where

  private
    extension = Field.ring extension-field

  field
    dimension : Nat
    basis :
      HasBasis
        (Field.ring base-field)
        extension
        algebra-map
        dimension

    automorphism-count : Nat
    automorphism :
      Fin automorphism-count →
      KAutomorphism base-field extension-field algebra-map
    automorphism-complete :
      (φ : KAutomorphism base-field extension-field algebra-map) →
      Σ (Fin automorphism-count)
        (λ i → AutomorphismEqual (automorphism i) φ)
    automorphism-distinct :
      (i j : Fin automorphism-count) →
      AutomorphismEqual (automorphism i) (automorphism j) →
      i ≡ j

    fixed-elements-are-scalars :
      (x : L) →
      ((i : Fin automorphism-count) →
        KAutomorphism.apply (automorphism i) x ≡ x) →
      Σ K (λ scalar → RingHom.map algebra-map scalar ≡ x)

GaloisNorm :
  {k l : Level} →
  {K : Set k} →
  {L : Set l} →
  {base-field : Field K} →
  {extension-field : Field L} →
  {algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)} →
  FiniteGaloisExtension base-field extension-field algebra-map →
  L →
  L
GaloisNorm {extension-field = extension-field} galois x =
  productFin
    (Field.ring extension-field)
    (FiniteGaloisExtension.automorphism-count galois)
    (λ i →
      KAutomorphism.apply
        (FiniteGaloisExtension.automorphism galois i)
        x)

AutomorphismsAreCyclic :
  {k l : Level} →
  {K : Set k} →
  {L : Set l} →
  {base-field : Field K} →
  {extension-field : Field L} →
  {algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)} →
  FiniteGaloisExtension base-field extension-field algebra-map →
  Set (k ⊔ l)
AutomorphismsAreCyclic
  {base-field = base-field}
  {extension-field = extension-field}
  {algebra-map = algebra-map}
  galois =
  Σ (KAutomorphism base-field extension-field algebra-map)
    (λ generator →
      (φ : KAutomorphism base-field extension-field algebra-map) →
      GeneratedBy generator φ)

hilbert-theorem-90 : Setω
hilbert-theorem-90 =
  ∀ {k l : Level} →
  (K : Set k) →
  (L : Set l) →
  (base-field : Field K) →
  (extension-field : Field L) →
  (algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)) →
  (galois :
    FiniteGaloisExtension
      base-field
      extension-field
      algebra-map) →
  AutomorphismsAreCyclic galois →
  (g : KAutomorphism base-field extension-field algebra-map) →
  ((φ : KAutomorphism base-field extension-field algebra-map) →
    GeneratedBy g φ) →
  (x : L) →
  GaloisNorm galois x ≡
    CommutativeRing.one (Field.ring extension-field) →
  Σ L
    (λ y →
      (y ≠ CommutativeRing.zero (Field.ring extension-field))
      ×
      (CommutativeRing.multiply
        (Field.ring extension-field)
        y
        (Field.inverse extension-field
          (KAutomorphism.apply g y))
      ≡
      x))
