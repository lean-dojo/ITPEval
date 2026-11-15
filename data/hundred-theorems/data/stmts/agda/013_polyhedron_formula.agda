-- Statement-only formalization of "Polyhedron Formula" from Hundred Theorems item 013
-- (artifact hundred-theorems__agda__013): a full-dimensional convex polytope in real
-- three-space has V - E + F = 2. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _≠_ _≈_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {a : Level} {A : Set a} → A → A → Set a
x ≠ y = x ≡ y → ⊥

record _∧_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists {a p : Level} (A : Set a) (P : A → Set p) :
    Set (a ⊔ p) where
  constructor witness
  field
    value    : A
    evidence : P value

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

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
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
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

record Point3 (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R
    z-coordinate : R

Region : Set → Set₁
Region A = A → Set

_≈_ : {A : Set} → Region A → Region A → Set
_≈_ {A = A} S T = (x : A) → S x ↔ T x

record HasCardinality
  {a e p : Level}
  {A : Set a}
  (equivalent : A → A → Set e)
  (P : A → Set p)
  (cardinality : Nat) : Set (a ⊔ e ⊔ p) where

  field
    enumerate : Fin cardinality → A

    enumeration-sound :
      (i : Fin cardinality) →
      P (enumerate i)

    enumeration-complete :
      (item : A) →
      P item →
      Exists (Fin cardinality) (λ i → equivalent item (enumerate i))

    enumeration-injective :
      (i j : Fin cardinality) →
      equivalent (enumerate i) (enumerate j) →
      i ≡ j

module PolyhedronFormulaStatement
  {R : Set}
  (reals : CompleteOrderedField R) where

  open CompleteOrderedField reals
  open Point3

  Point : Set
  Point = Point3 R

  Region3 : Set₁
  Region3 = Region Point

  zeroPoint : Point
  zeroPoint = point zeroR zeroR zeroR

  addPoint : Point → Point → Point
  addPoint u v =
    point
      (add (x-coordinate u) (x-coordinate v))
      (add (y-coordinate u) (y-coordinate v))
      (add (z-coordinate u) (z-coordinate v))

  negatePoint : Point → Point
  negatePoint u =
    point
      (negate (x-coordinate u))
      (negate (y-coordinate u))
      (negate (z-coordinate u))

  subtractPoint : Point → Point → Point
  subtractPoint u v = addPoint u (negatePoint v)

  scalePoint : R → Point → Point
  scalePoint scalar u =
    point
      (multiply scalar (x-coordinate u))
      (multiply scalar (y-coordinate u))
      (multiply scalar (z-coordinate u))

  dot : Point → Point → R
  dot u v =
    add
      (add
        (multiply (x-coordinate u) (x-coordinate v))
        (multiply (y-coordinate u) (y-coordinate v)))
      (multiply (z-coordinate u) (z-coordinate v))

  sumFin : {n : Nat} → (Fin n → R) → R
  sumFin {zero} values = zeroR
  sumFin {suc n} values =
    add (values fzero) (sumFin (λ i → values (fsuc i)))

  weightedSum :
    {n : Nat} →
    (Fin n → Point) →
    (Fin n → R) →
    Point
  weightedSum {zero} vertices weights = zeroPoint
  weightedSum {suc n} vertices weights =
    addPoint
      (scalePoint (weights fzero) (vertices fzero))
      (weightedSum
        (λ i → vertices (fsuc i))
        (λ i → weights (fsuc i)))

  convexHull :
    {n : Nat} →
    (Fin n → Point) →
    Region3
  convexHull {n} vertices p =
    Exists (Fin n → R)
      (λ weights →
        ((i : Fin n) → lessOrEqual zeroR (weights i)) ∧
        (sumFin weights ≡ oneR) ∧
        (weightedSum vertices weights ≡ p))

  Polytope : Region3 → Set
  Polytope polyhedron =
    Exists Nat
      (λ n →
        Exists (Fin n → Point)
          (λ vertices → polyhedron ≈ convexHull vertices))

  faceOf : Region3 → Region3 → Set
  faceOf face polyhedron =
    Exists Point
      (λ normal →
        Exists R
          (λ bound →
            ((p : Point) →
              polyhedron p →
              lessOrEqual (dot normal p) bound) ∧
            (face ≈
              (λ p →
                polyhedron p ∧ dot normal p ≡ bound))))

  linearlyIndependent2 : Point → Point → Set
  linearlyIndependent2 u v =
    (a b : R) →
    addPoint (scalePoint a u) (scalePoint b v) ≡ zeroPoint →
    a ≡ zeroR ∧ b ≡ zeroR

  linearlyIndependent3 : Point → Point → Point → Set
  linearlyIndependent3 u v w =
    (a b c : R) →
    addPoint
      (addPoint (scalePoint a u) (scalePoint b v))
      (scalePoint c w) ≡ zeroPoint →
    a ≡ zeroR ∧ b ≡ zeroR ∧ c ≡ zeroR

  affineDimensionZero : Region3 → Set
  affineDimensionZero S =
    Exists Point
      (λ p →
        S p ∧
        ((q : Point) → S q → q ≡ p))

  affineDimensionOne : Region3 → Set
  affineDimensionOne S =
    Exists Point
      (λ p →
        Exists Point
          (λ q →
            S p ∧
            S q ∧
            p ≠ q ∧
            ((r : Point) →
              S r →
              Exists R
                (λ t →
                  r ≡
                  addPoint p
                    (scalePoint t (subtractPoint q p))))))

  affineDimensionTwo : Region3 → Set
  affineDimensionTwo S =
    Exists Point
      (λ p →
        Exists Point
          (λ q →
            Exists Point
              (λ r →
                S p ∧
                S q ∧
                S r ∧
                linearlyIndependent2
                  (subtractPoint q p)
                  (subtractPoint r p) ∧
                ((s : Point) →
                  S s →
                  Exists R
                    (λ a →
                      Exists R
                        (λ b →
                          s ≡
                          addPoint
                            (addPoint p
                              (scalePoint a (subtractPoint q p)))
                            (scalePoint b (subtractPoint r p))))))))

  affineDimensionThree : Region3 → Set
  affineDimensionThree S =
    Exists Point
      (λ p →
        Exists Point
          (λ q →
            Exists Point
              (λ r →
                Exists Point
                  (λ s →
                    S p ∧
                    S q ∧
                    S r ∧
                    S s ∧
                    linearlyIndependent3
                      (subtractPoint q p)
                      (subtractPoint r p)
                      (subtractPoint s p)))))

  vertexFace : Region3 → Region3 → Set
  vertexFace polyhedron face =
    faceOf face polyhedron ∧ affineDimensionZero face

  edgeFace : Region3 → Region3 → Set
  edgeFace polyhedron face =
    faceOf face polyhedron ∧ affineDimensionOne face

  twoDimensionalFace : Region3 → Region3 → Set
  twoDimensionalFace polyhedron face =
    faceOf face polyhedron ∧ affineDimensionTwo face

  record EulerFaceCounts (polyhedron : Region3) : Set₁ where
    field
      vertexCount edgeCount twoDimensionalFaceCount : Nat

      vertex-cardinality :
        HasCardinality
          (λ S T → S ≈ T)
          (vertexFace polyhedron)
          vertexCount

      edge-cardinality :
        HasCardinality
          (λ S T → S ≈ T)
          (edgeFace polyhedron)
          edgeCount

      two-dimensional-face-cardinality :
        HasCardinality
          (λ S T → S ≈ T)
          (twoDimensionalFace polyhedron)
          twoDimensionalFaceCount

      Euler-relation :
        vertexCount + twoDimensionalFaceCount - edgeCount ≡ suc (suc zero)

  proposition : Set₁
  proposition =
    (polyhedron : Region3) →
    Polytope polyhedron →
    affineDimensionThree polyhedron →
    EulerFaceCounts polyhedron

polyhedron-formula : Set₁
polyhedron-formula =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  PolyhedronFormulaStatement.proposition reals
