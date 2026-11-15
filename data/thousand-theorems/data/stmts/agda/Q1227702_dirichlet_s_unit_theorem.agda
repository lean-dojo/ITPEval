-- Statement-only formalization of thousand-theorems corpus artifact Q1227702,
-- "Dirichlet's unit theorem": the units of a number field's ring of integers
-- have a basis modulo torsion, giving a unique root-of-unity times
-- integer-powers decomposition. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1227702_dirichlet_s_unit_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infixr 4 _×_
infixr 3 _∨_
infix 4 _≠_

data Bottom {a : Level} : Set a where

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
_≠_ {a} x y =
  x ≡ y → Bottom {a}

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    first  : A
    second : B

data _∨_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A ∨ B
  right : B → A ∨ B

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

record CommutativeRing
  {a : Level}
  (R : Set a) :
  Set a where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zero-left :
      (x : R) →
      addR zeroR x ≡ x
    add-zero-right :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse-left :
      (x : R) →
      addR (negateR x) x ≡ zeroR
    add-inverse-right :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-one-left :
      (x : R) →
      multiplyR oneR x ≡ x
    multiply-one-right :
      (x : R) →
      multiplyR x oneR ≡ x
    distribute-left :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) →
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

record Field
  {a : Level}
  (K : Set a) :
  Set a where

  field
    ring : CommutativeRing K
    inverseK : K → K
    one-not-zero :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    inverse-law :
      (x : K) →
      x ≠ CommutativeRing.zeroR ring →
      CommutativeRing.multiplyR ring x (inverseK x) ≡
      CommutativeRing.oneR ring

record RingHom
  {a b : Level}
  {R : Set a}
  {S : Set b}
  (domain : CommutativeRing R)
  (codomain : CommutativeRing S) :
  Set (a ⊔ b) where

  field
    map : R → S
    map-zero :
      map (CommutativeRing.zeroR domain) ≡
      CommutativeRing.zeroR codomain
    map-one :
      map (CommutativeRing.oneR domain) ≡
      CommutativeRing.oneR codomain
    map-add :
      (x y : R) →
      map (CommutativeRing.addR domain x y) ≡
      CommutativeRing.addR codomain (map x) (map y)
    map-multiply :
      (x y : R) →
      map (CommutativeRing.multiplyR domain x y) ≡
      CommutativeRing.multiplyR codomain (map x) (map y)

record FieldEmbedding
  {a b : Level}
  {K : Set a}
  {L : Set b}
  (domain : Field K)
  (codomain : Field L) :
  Set (a ⊔ b) where

  field
    hom : RingHom (Field.ring domain) (Field.ring codomain)
    injective :
      (x y : K) →
      RingHom.map hom x ≡ RingHom.map hom y →
      x ≡ y

fromNat :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Nat →
  R
fromNat ring zero =
  CommutativeRing.zeroR ring
fromNat ring (suc n) =
  CommutativeRing.addR ring
    (fromNat ring n)
    (CommutativeRing.oneR ring)

fromInt :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  Int →
  R
fromInt ring (pos n) =
  fromNat ring n
fromInt ring (negsuc n) =
  CommutativeRing.negateR ring
    (fromNat ring (suc n))

power :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  R →
  Nat →
  R
power ring x zero =
  CommutativeRing.oneR ring
power ring x (suc n) =
  CommutativeRing.multiplyR ring x (power ring x n)

evaluateMonic :
  {a : Level} →
  {K : Set a} →
  CommutativeRing K →
  List Int →
  K →
  K
evaluateMonic ring [] x =
  CommutativeRing.oneR ring
evaluateMonic ring (coefficient ∷ coefficients) x =
  CommutativeRing.addR ring
    (fromInt ring coefficient)
    (CommutativeRing.multiplyR ring x
      (evaluateMonic ring coefficients x))

IntegralOverIntegers :
  {a : Level} →
  {K : Set a} →
  Field K →
  K →
  Set a
IntegralOverIntegers field-structure x =
  Σ (List Int)
    (λ coefficients →
      evaluateMonic
        (Field.ring field-structure)
        coefficients
        x
      ≡
      CommutativeRing.zeroR (Field.ring field-structure))

sumFin :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  (n : Nat) →
  (Fin n → R) →
  R
sumFin ring zero terms =
  CommutativeRing.zeroR ring
sumFin ring (suc n) terms =
  CommutativeRing.addR ring
    (terms fzero)
    (sumFin ring n (λ i → terms (fsuc i)))

record RationalField
  {q : Level}
  (Q : Set q)
  (field-structure : Field Q) :
  Set q where

  field
    characteristic-zero :
      (m n : Nat) →
      fromNat (Field.ring field-structure) m ≡
      fromNat (Field.ring field-structure) n →
      m ≡ n
    every-element-is-a-fraction :
      (x : Q) →
      Σ Int
        (λ numerator →
          Σ Nat
            (λ denominator-minus-one →
              CommutativeRing.multiplyR
                (Field.ring field-structure)
                x
                (fromNat
                  (Field.ring field-structure)
                  (suc denominator-minus-one))
              ≡
              fromInt (Field.ring field-structure) numerator))

record FiniteRationalBasis
  {q k : Level}
  {Q : Set q}
  {K : Set k}
  (rationalField : Field Q)
  (numberField : Field K)
  (inclusion :
    FieldEmbedding rationalField numberField) :
  Set (q ⊔ k) where

  open CommutativeRing (Field.ring numberField)

  field
    dimension : Nat
    vector : Fin dimension → K
    coordinates : K → Fin dimension → Q
    reconstruct :
      (x : K) →
      sumFin
        (Field.ring numberField)
        dimension
        (λ i →
          multiplyR
            (RingHom.map
              (FieldEmbedding.hom inclusion)
              (coordinates x i))
            (vector i))
      ≡
      x
    coordinates-unique :
      (x : K) →
      (coefficients : Fin dimension → Q) →
      sumFin
        (Field.ring numberField)
        dimension
        (λ i →
          multiplyR
            (RingHom.map
              (FieldEmbedding.hom inclusion)
              (coefficients i))
            (vector i))
      ≡
      x →
      (i : Fin dimension) →
      coefficients i ≡ coordinates x i

record RingOfIntegers
  {k o : Level}
  {K : Set k}
  (numberField : Field K)
  (O : Set o) :
  Set (k ⊔ o) where

  field
    ring : CommutativeRing O
    inclusion :
      RingHom ring (Field.ring numberField)
    inclusion-injective :
      (x y : O) →
      RingHom.map inclusion x ≡ RingHom.map inclusion y →
      x ≡ y
    image-is-integral :
      (x : O) →
      IntegralOverIntegers numberField
        (RingHom.map inclusion x)
    contains-every-integral-element :
      (x : K) →
      IntegralOverIntegers numberField x →
      Σ O
        (λ y → RingHom.map inclusion y ≡ x)

record CommutativeGroup
  {u : Level}
  (U : Set u) :
  Set u where

  field
    identity : U
    inverse : U → U
    multiply : U → U → U
    associative :
      (x y z : U) →
      multiply x (multiply y z) ≡
      multiply (multiply x y) z
    identity-left :
      (x : U) →
      multiply identity x ≡ x
    identity-right :
      (x : U) →
      multiply x identity ≡ x
    inverse-left :
      (x : U) →
      multiply (inverse x) x ≡ identity
    inverse-right :
      (x : U) →
      multiply x (inverse x) ≡ identity
    commutative :
      (x y : U) →
      multiply x y ≡ multiply y x

groupPower :
  {u : Level} →
  {U : Set u} →
  CommutativeGroup U →
  U →
  Nat →
  U
groupPower group x zero =
  CommutativeGroup.identity group
groupPower group x (suc n) =
  CommutativeGroup.multiply group x
    (groupPower group x n)

integerPower :
  {u : Level} →
  {U : Set u} →
  CommutativeGroup U →
  U →
  Int →
  U
integerPower group x (pos n) =
  groupPower group x n
integerPower group x (negsuc n) =
  groupPower group
    (CommutativeGroup.inverse group x)
    (suc n)

groupProductFin :
  {u : Level} →
  {U : Set u} →
  CommutativeGroup U →
  (n : Nat) →
  (Fin n → U) →
  U
groupProductFin group zero terms =
  CommutativeGroup.identity group
groupProductFin group (suc n) terms =
  CommutativeGroup.multiply group
    (terms fzero)
    (groupProductFin group n (λ i → terms (fsuc i)))

record UnitGroupOf
  {o u : Level}
  {O : Set o}
  (ring : CommutativeRing O)
  (U : Set u) :
  Set (o ⊔ u) where

  field
    group : CommutativeGroup U
    value inverse-value : U → O
    value-identity :
      value (CommutativeGroup.identity group) ≡
      CommutativeRing.oneR ring
    value-multiply :
      (x y : U) →
      value (CommutativeGroup.multiply group x y) ≡
      CommutativeRing.multiplyR ring (value x) (value y)
    value-inverse :
      (x : U) →
      value (CommutativeGroup.inverse group x) ≡
      inverse-value x
    unit-law :
      (x : U) →
      CommutativeRing.multiplyR ring
        (value x)
        (inverse-value x)
      ≡
      CommutativeRing.oneR ring
    value-injective :
      (x y : U) →
      value x ≡ value y →
      x ≡ y
    every-unit-is-represented :
      (x y : O) →
      CommutativeRing.multiplyR ring x y ≡
      CommutativeRing.oneR ring →
      Σ U (λ unit → value unit ≡ x)

-- Complete Archimedean ordered fields present the standard real numbers
-- uniquely up to ordered-field isomorphism.
record CompleteArchimedeanOrderedField
  {r : Level}
  (R : Set r)
  (real-field : Field R) :
  Set (lsuc r) where

  open CommutativeRing (Field.ring real-field)

  field
    less-or-equal : R → R → Set r
    order-reflexive :
      (x : R) →
      less-or-equal x x
    order-transitive :
      (x y z : R) →
      less-or-equal x y →
      less-or-equal y z →
      less-or-equal x z
    order-antisymmetric :
      (x y : R) →
      less-or-equal x y →
      less-or-equal y x →
      x ≡ y
    order-total :
      (x y : R) →
      less-or-equal x y ∨ less-or-equal y x
    add-order :
      (x y z : R) →
      less-or-equal x y →
      less-or-equal (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) →
      less-or-equal zeroR x →
      less-or-equal zeroR y →
      less-or-equal zeroR (multiplyR x y)
    zero-less-than-one :
      less-or-equal zeroR oneR × (oneR ≠ zeroR)
    archimedean :
      (x : R) →
      Σ Nat
        (λ n →
          less-or-equal x
            (fromNat (Field.ring real-field) n))
    least-upper-bound :
      (P : R → Set r) →
      Σ R P →
      Σ R
        (λ upper →
          (x : R) →
          P x →
          less-or-equal x upper) →
      Σ R
        (λ supremum →
          ((x : R) →
            P x →
            less-or-equal x supremum)
          ×
          ((upper : R) →
            ((x : R) →
              P x →
              less-or-equal x upper) →
            less-or-equal supremum upper))

record Complex
  {r : Level}
  (R : Set r) :
  Set r where

  constructor complex
  field
    real-part : R
    imaginary-part : R

complexZero :
  {r : Level} →
  {R : Set r} →
  Field R →
  Complex R
complexZero real-field =
  complex
    (CommutativeRing.zeroR (Field.ring real-field))
    (CommutativeRing.zeroR (Field.ring real-field))

complexOne :
  {r : Level} →
  {R : Set r} →
  Field R →
  Complex R
complexOne real-field =
  complex
    (CommutativeRing.oneR (Field.ring real-field))
    (CommutativeRing.zeroR (Field.ring real-field))

complexAdd :
  {r : Level} →
  {R : Set r} →
  Field R →
  Complex R →
  Complex R →
  Complex R
complexAdd real-field (complex a b) (complex c d) =
  let ring = Field.ring real-field
  in
  complex
    (CommutativeRing.addR ring a c)
    (CommutativeRing.addR ring b d)

complexNegate :
  {r : Level} →
  {R : Set r} →
  Field R →
  Complex R →
  Complex R
complexNegate real-field (complex a b) =
  let ring = Field.ring real-field
  in
  complex
    (CommutativeRing.negateR ring a)
    (CommutativeRing.negateR ring b)

complexMultiply :
  {r : Level} →
  {R : Set r} →
  Field R →
  Complex R →
  Complex R →
  Complex R
complexMultiply real-field (complex a b) (complex c d) =
  let ring = Field.ring real-field
  in
  complex
    (CommutativeRing.addR ring
      (CommutativeRing.multiplyR ring a c)
      (CommutativeRing.negateR ring
        (CommutativeRing.multiplyR ring b d)))
    (CommutativeRing.addR ring
      (CommutativeRing.multiplyR ring a d)
      (CommutativeRing.multiplyR ring b c))

complexConjugate :
  {r : Level} →
  {R : Set r} →
  Field R →
  Complex R →
  Complex R
complexConjugate real-field (complex a b) =
  complex a
    (CommutativeRing.negateR
      (Field.ring real-field) b)

record StandardComplexField
  {r : Level}
  {R : Set r}
  (real-field : Field R) :
  Set (lsuc r) where

  field
    field-structure : Field (Complex R)
    zero-is-standard :
      CommutativeRing.zeroR (Field.ring field-structure) ≡
      complexZero real-field
    one-is-standard :
      CommutativeRing.oneR (Field.ring field-structure) ≡
      complexOne real-field
    add-is-standard :
      (z w : Complex R) →
      CommutativeRing.addR
        (Field.ring field-structure) z w
      ≡
      complexAdd real-field z w
    multiply-is-standard :
      (z w : Complex R) →
      CommutativeRing.multiplyR
        (Field.ring field-structure) z w
      ≡
      complexMultiply real-field z w
    negate-is-standard :
      (z : Complex R) →
      CommutativeRing.negateR
        (Field.ring field-structure) z
      ≡
      complexNegate real-field z

PointwiseEqual :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  (A → B) →
  Set (a ⊔ b)
PointwiseEqual f g =
  (x : _) → f x ≡ g x

record InfinitePlaces
  {k r p : Level}
  {K : Set k}
  {R : Set r}
  (numberField : Field K)
  (real-field : Field R)
  (real-numbers :
    CompleteArchimedeanOrderedField R real-field)
  (complex-numbers : StandardComplexField real-field)
  (P : Set p) :
  Set (lsuc (k ⊔ r ⊔ p)) where

  field
    representative :
      P →
      FieldEmbedding numberField
        (StandardComplexField.field-structure complex-numbers)
    place-count : Nat
    finite-places :
      Bijection P (Fin place-count)
    complete-up-to-conjugation :
      (embedding :
        FieldEmbedding numberField
          (StandardComplexField.field-structure complex-numbers)) →
      Σ P
        (λ place →
          PointwiseEqual
            (λ x →
              RingHom.map
                (FieldEmbedding.hom embedding) x)
            (λ x →
              RingHom.map
                (FieldEmbedding.hom
                  (representative place)) x)
          ∨
          PointwiseEqual
            (λ x →
              RingHom.map
                (FieldEmbedding.hom embedding) x)
            (λ x →
              complexConjugate real-field
                (RingHom.map
                  (FieldEmbedding.hom
                    (representative place)) x)))
    no-duplicate-places :
      (p q : P) →
      (PointwiseEqual
        (λ x →
          RingHom.map
            (FieldEmbedding.hom (representative p)) x)
        (λ x →
          RingHom.map
            (FieldEmbedding.hom (representative q)) x)
      ∨
      PointwiseEqual
        (λ x →
          RingHom.map
            (FieldEmbedding.hom (representative p)) x)
        (λ x →
          complexConjugate real-field
            (RingHom.map
              (FieldEmbedding.hom
                (representative q)) x))) →
      p ≡ q

record NumberFieldUnitData
  {q k o u r p : Level}
  (Q : Set q)
  (K : Set k)
  (O : Set o)
  (U : Set u)
  (R : Set r)
  (P : Set p) :
  Set (lsuc (q ⊔ k ⊔ o ⊔ u ⊔ r ⊔ p)) where

  field
    rational-field : Field Q
    rationals : RationalField Q rational-field
    number-field : Field K
    rational-inclusion :
      FieldEmbedding rational-field number-field
    finite-dimensional :
      FiniteRationalBasis
        rational-field
        number-field
        rational-inclusion
    ring-of-integers :
      RingOfIntegers number-field O
    unit-group :
      UnitGroupOf
        (RingOfIntegers.ring ring-of-integers)
        U
    real-field : Field R
    real-numbers :
      CompleteArchimedeanOrderedField R real-field
    complex-numbers :
      StandardComplexField real-field
    infinite-places :
      InfinitePlaces
        number-field
        real-field
        real-numbers
        complex-numbers
        P

Torsion :
  {u : Level} →
  {U : Set u} →
  CommutativeGroup U →
  U →
  Set u
Torsion group x =
  Σ Nat
    (λ exponent-minus-one →
      groupPower group x (suc exponent-minus-one) ≡
      CommutativeGroup.identity group)

record Coordinates
  {u : Level}
  {U : Set u}
  (group : CommutativeGroup U)
  (rank : Nat) :
  Set u where

  constructor coordinates
  field
    torsion-unit : U
    torsion-proof : Torsion group torsion-unit
    exponents : Fin rank → Int

Decomposes :
  {u : Level} →
  {U : Set u} →
  (group : CommutativeGroup U) →
  (rank : Nat) →
  (fundamental-system : Fin rank → U) →
  U →
  Coordinates group rank →
  Set u
Decomposes group rank fundamental-system x coordinate-data =
  x ≡
  CommutativeGroup.multiply group
    (Coordinates.torsion-unit coordinate-data)
    (groupProductFin group rank
      (λ i →
        integerPower group
          (fundamental-system i)
          (Coordinates.exponents coordinate-data i)))

record SameCoordinates
  {u : Level}
  {U : Set u}
  {group : CommutativeGroup U}
  {rank : Nat}
  (left-coordinate right-coordinate :
    Coordinates group rank) :
  Set u where

  field
    same-torsion-unit :
      Coordinates.torsion-unit left-coordinate ≡
      Coordinates.torsion-unit right-coordinate
    same-exponents :
      (i : Fin rank) →
      Coordinates.exponents left-coordinate i ≡
      Coordinates.exponents right-coordinate i

UniqueDecomposition :
  {u : Level} →
  {U : Set u} →
  (group : CommutativeGroup U) →
  (rank : Nat) →
  (fundamental-system : Fin rank → U) →
  U →
  Set u
UniqueDecomposition group rank fundamental-system x =
  Σ (Coordinates group rank)
    (λ coordinate-data →
      Decomposes
        group rank fundamental-system x coordinate-data
      ×
      ((other-coordinate-data : Coordinates group rank) →
        Decomposes
          group rank fundamental-system x other-coordinate-data →
        SameCoordinates coordinate-data other-coordinate-data))

record BasisModuloTorsion
  {u : Level}
  {U : Set u}
  (group : CommutativeGroup U)
  (rank : Nat)
  (fundamental-system : Fin rank → U) :
  Set u where

  field
    unique-expansion :
      (x : U) →
      UniqueDecomposition group rank fundamental-system x

-- Lean: NumberField.Units.basisModTorsion and
-- NumberField.Units.exist_unique_eq_mul_prod
dirichlet-unit-theorem :
  (q k o u r p : Level) →
  Set (lsuc (q ⊔ k ⊔ o ⊔ u ⊔ r ⊔ p))
dirichlet-unit-theorem q k o u r p =
  (Q : Set q) →
  (K : Set k) →
  (O : Set o) →
  (U : Set u) →
  (R : Set r) →
  (P : Set p) →
  (number-field-data : NumberFieldUnitData Q K O U R P) →
  let group =
        UnitGroupOf.group
          (NumberFieldUnitData.unit-group number-field-data)
      rank =
        predecessor
          (InfinitePlaces.place-count
            (NumberFieldUnitData.infinite-places number-field-data))
  in
  Σ (Fin rank → U)
    (λ fundamental-system →
      BasisModuloTorsion group rank fundamental-system)
