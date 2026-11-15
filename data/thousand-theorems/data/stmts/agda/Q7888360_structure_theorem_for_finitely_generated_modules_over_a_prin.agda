-- Statement-only formalization of thousand-theorems corpus artifact Q7888360,
-- "Structure theorem for finitely generated modules over a principal ideal domain":
-- a finitely generated module over a PID is linearly equivalent to a finite free
-- module times a finite direct sum of cyclic prime-power quotients. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q7888360_structure_theorem_for_finitely_generated_modules_over_a_prin where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 4 _×_
infixr 3 _⊎_
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

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} A =
  A → Bottom {a}

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    first  : A
    second : B

data _⊎_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A ⊎ B
  right : B → A ⊎ B

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    forward  : A → B
    backward : B → A

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

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size        : Nat
    equivalence : Bijection A (Fin size)

record CommutativeRing
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
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

    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
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

record IntegralDomain
  {r : Level}
  {R : Set r}
  (ring : CommutativeRing R) :
  Set r where

  field
    nontrivial :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    no-zero-divisors :
      (x y : R) →
      CommutativeRing.multiplyR ring x y ≡
      CommutativeRing.zeroR ring →
      x ≡ CommutativeRing.zeroR ring ⊎
      y ≡ CommutativeRing.zeroR ring

record Ideal
  {r : Level}
  {R : Set r}
  (ring : CommutativeRing R) :
  Set (lsuc r) where

  field
    member : R → Set r
    membership-propositional :
      (x : R) →
      (u v : member x) →
      u ≡ v
    contains-zero :
      member (CommutativeRing.zeroR ring)
    closed-under-addition :
      (x y : R) →
      member x →
      member y →
      member (CommutativeRing.addR ring x y)
    closed-under-negation :
      (x : R) →
      member x →
      member (CommutativeRing.negateR ring x)
    absorbs-multiplication :
      (a x : R) →
      member x →
      member (CommutativeRing.multiplyR ring a x)

IsPrincipal :
  {r : Level} →
  {R : Set r} →
  {ring : CommutativeRing R} →
  Ideal ring →
  Set r
IsPrincipal {R = R} {ring = ring} ideal =
  Σ R
    (λ generator →
      (x : R) →
      Ideal.member ideal x ↔
      Σ R
        (λ coefficient →
          x ≡
          CommutativeRing.multiplyR ring coefficient generator))

PrincipalIdealRing :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  Set (lsuc r)
PrincipalIdealRing ring =
  (ideal : Ideal ring) →
  IsPrincipal ideal

record Module
  {r m : Level}
  {R : Set r}
  (ring : CommutativeRing R)
  (M : Set m) :
  Set (r ⊔ m) where

  field
    zeroM : M
    addM  : M → M → M
    negateM : M → M
    scale : R → M → M

    add-associative :
      (x y z : M) →
      addM (addM x y) z ≡ addM x (addM y z)
    add-commutative :
      (x y : M) →
      addM x y ≡ addM y x
    add-zero-left :
      (x : M) →
      addM zeroM x ≡ x
    add-zero-right :
      (x : M) →
      addM x zeroM ≡ x
    add-inverse-left :
      (x : M) →
      addM (negateM x) x ≡ zeroM
    add-inverse-right :
      (x : M) →
      addM x (negateM x) ≡ zeroM

    one-scale :
      (x : M) →
      scale (CommutativeRing.oneR ring) x ≡ x
    multiply-scale :
      (a b : R) (x : M) →
      scale (CommutativeRing.multiplyR ring a b) x ≡
      scale a (scale b x)
    add-scale :
      (a b : R) (x : M) →
      scale (CommutativeRing.addR ring a b) x ≡
      addM (scale a x) (scale b x)
    scale-add :
      (a : R) (x y : M) →
      scale a (addM x y) ≡
      addM (scale a x) (scale a y)
    zero-scale :
      (x : M) →
      scale (CommutativeRing.zeroR ring) x ≡ zeroM
    scale-zero :
      (a : R) →
      scale a zeroM ≡ zeroM

sumFin :
  {r m : Level} →
  {R : Set r} →
  {M : Set m} →
  {ring : CommutativeRing R} →
  Module ring M →
  (n : Nat) →
  (Fin n → M) →
  M
sumFin module-structure zero terms =
  Module.zeroM module-structure
sumFin module-structure (suc n) terms =
  Module.addM module-structure
    (terms fzero)
    (sumFin module-structure n (λ i → terms (fsuc i)))

FinitelyGenerated :
  {r m : Level} →
  {R : Set r} →
  {M : Set m} →
  {ring : CommutativeRing R} →
  Module ring M →
  Set (r ⊔ m)
FinitelyGenerated {R = R} {M = M} module-structure =
  Σ Nat
    (λ number-of-generators →
      Σ (Fin number-of-generators → M)
        (λ generators →
          (x : M) →
          Σ (Fin number-of-generators → R)
            (λ coefficients →
              x ≡
              sumFin module-structure number-of-generators
                (λ i →
                  Module.scale module-structure
                    (coefficients i)
                    (generators i)))))

power :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  R →
  Nat →
  R
power ring x zero =
  CommutativeRing.oneR ring
power ring x (suc n) =
  CommutativeRing.multiplyR ring x (power ring x n)

Unit :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  R →
  Set r
Unit {R = R} ring x =
  Σ R
    (λ inverse →
      CommutativeRing.multiplyR ring x inverse ≡
      CommutativeRing.oneR ring)

Irreducible :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  R →
  Set r
Irreducible {R = R} ring p =
  Not (Unit ring p) ×
  ((x y : R) →
    CommutativeRing.multiplyR ring x y ≡ p →
    Unit ring x ⊎ Unit ring y)

record Coordinates
  {r i : Level}
  (n : Nat)
  (Index : Set i)
  (R : Set r) :
  Set (r ⊔ i) where

  constructor coordinates
  field
    free-part    : Fin n → R
    torsion-part : Index → R

addCoordinates :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  (ring : CommutativeRing R) →
  {n : Nat} →
  Coordinates n Index R →
  Coordinates n Index R →
  Coordinates n Index R
addCoordinates ring left-coordinate right-coordinate =
  coordinates
    (λ j →
      CommutativeRing.addR ring
        (Coordinates.free-part left-coordinate j)
        (Coordinates.free-part right-coordinate j))
    (λ i →
      CommutativeRing.addR ring
        (Coordinates.torsion-part left-coordinate i)
        (Coordinates.torsion-part right-coordinate i))

scaleCoordinates :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  (ring : CommutativeRing R) →
  {n : Nat} →
  R →
  Coordinates n Index R →
  Coordinates n Index R
scaleCoordinates ring scalar coordinate =
  coordinates
    (λ j →
      CommutativeRing.multiplyR ring scalar
        (Coordinates.free-part coordinate j))
    (λ i →
      CommutativeRing.multiplyR ring scalar
        (Coordinates.torsion-part coordinate i))

PrincipalCongruent :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  R →
  R →
  R →
  Set r
PrincipalCongruent {R = R} ring generator x y =
  Σ R
    (λ coefficient →
      x ≡
      CommutativeRing.addR ring y
        (CommutativeRing.multiplyR ring coefficient generator))

CoordinateEquivalent :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  (ring : CommutativeRing R) →
  {n : Nat} →
  (prime : Index → R) →
  (exponent : Index → Nat) →
  Coordinates n Index R →
  Coordinates n Index R →
  Set (r ⊔ i)
CoordinateEquivalent ring prime exponent left-coordinate right-coordinate =
  ((j : Fin _) →
    Coordinates.free-part left-coordinate j ≡
    Coordinates.free-part right-coordinate j) ×
  ((i : _) →
    PrincipalCongruent ring
      (power ring (prime i) (exponent i))
      (Coordinates.torsion-part left-coordinate i)
      (Coordinates.torsion-part right-coordinate i))

-- This record presents a linear equivalence to the quotient setoid of the
-- coordinates. For finite Index, all indexed families have finite support,
-- so the torsion coordinates are exactly the finite direct sum in the source.
record LinearEquivalenceToDecomposition
  {r m i : Level}
  {R : Set r}
  {M : Set m}
  {Index : Set i}
  (ring : CommutativeRing R)
  (module-structure : Module ring M)
  (n : Nat)
  (prime : Index → R)
  (exponent : Index → Nat) :
  Set (r ⊔ m ⊔ i) where

  field
    map :
      M →
      Coordinates n Index R
    map-add :
      (x y : M) →
      CoordinateEquivalent ring prime exponent
        (map (Module.addM module-structure x y))
        (addCoordinates ring (map x) (map y))
    map-scale :
      (a : R) (x : M) →
      CoordinateEquivalent ring prime exponent
        (map (Module.scale module-structure a x))
        (scaleCoordinates ring a (map x))
    injective :
      (x y : M) →
      CoordinateEquivalent ring prime exponent (map x) (map y) →
      x ≡ y
    surjective :
      (coordinate : Coordinates n Index R) →
      Σ M
        (λ x →
          CoordinateEquivalent ring prime exponent
            (map x) coordinate)

-- Lean: Module.equiv_free_prod_directSum
structure-theorem-for-finitely-generated-modules-over-a-pid :
  (r m : Level) →
  Set (lsuc r ⊔ lsuc m)
structure-theorem-for-finitely-generated-modules-over-a-pid r m =
  {R : Set r} →
  {M : Set m} →
  (ring : CommutativeRing R) →
  IntegralDomain ring →
  PrincipalIdealRing ring →
  (module-structure : Module ring M) →
  FinitelyGenerated module-structure →
  Σ Nat
    (λ free-rank →
      Σ (Set r)
        (λ Index →
          Σ (Finite Index)
            (λ finite-index →
              Σ (Index → R)
                (λ prime →
                  ((i : Index) → Irreducible ring (prime i)) ×
                  Σ (Index → Nat)
                    (λ exponent →
                      LinearEquivalenceToDecomposition
                        ring module-structure free-rank
                        prime exponent)))))
