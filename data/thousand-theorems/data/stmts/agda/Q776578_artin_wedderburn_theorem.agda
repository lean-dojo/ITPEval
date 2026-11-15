-- Statement-only formalization of thousand-theorems corpus artifact Q776578,
-- "Artin–Wedderburn theorem": a semisimple algebra is algebra-equivalent to a finite
-- product of matrix algebras over division algebras. This file contains no proof.

{-# OPTIONS --safe #-}

module Q776578_artin_wedderburn_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
  renaming (zero to zeroN; suc to sucN)
open import Agda.Builtin.Sigma using (Σ)

data Empty : Set where

Not : {a : Level} → Set a → Set a
Not A = A → Empty

infix 4 _≠_

_≠_ : {a : Level} {A : Set a} → A → A → Set a
x ≠ y = Not (x ≡ y)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (sucN n)
  fsuc  : {n : Nat} → Fin n → Fin (sucN n)

record CommutativeSemiring {a : Level} (A : Set a) : Set a where
  field
    zero one : A
    add multiply : A → A → A

    add-associative :
      (x y z : A) → add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : A) → add x y ≡ add y x
    add-zero-left :
      (x : A) → add zero x ≡ x
    add-zero-right :
      (x : A) → add x zero ≡ x

    multiply-associative :
      (x y z : A) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-commutative :
      (x y : A) → multiply x y ≡ multiply y x
    multiply-one-left :
      (x : A) → multiply one x ≡ x
    multiply-one-right :
      (x : A) → multiply x one ≡ x
    multiply-zero-left :
      (x : A) → multiply zero x ≡ zero
    multiply-zero-right :
      (x : A) → multiply x zero ≡ zero

    distribute-left :
      (x y z : A) →
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : A) →
      multiply (add x y) z ≡ add (multiply x z) (multiply y z)

record Ring {a : Level} (A : Set a) : Set a where
  field
    zero one : A
    add multiply : A → A → A
    negate : A → A

    add-associative :
      (x y z : A) → add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : A) → add x y ≡ add y x
    add-zero-left :
      (x : A) → add zero x ≡ x
    add-zero-right :
      (x : A) → add x zero ≡ x
    add-inverse-left :
      (x : A) → add (negate x) x ≡ zero
    add-inverse-right :
      (x : A) → add x (negate x) ≡ zero

    multiply-associative :
      (x y z : A) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one-left :
      (x : A) → multiply one x ≡ x
    multiply-one-right :
      (x : A) → multiply x one ≡ x
    multiply-zero-left :
      (x : A) → multiply zero x ≡ zero
    multiply-zero-right :
      (x : A) → multiply x zero ≡ zero

    distribute-left :
      (x y z : A) →
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : A) →
      multiply (add x y) z ≡ add (multiply x z) (multiply y z)

record DivisionRing {a : Level} (A : Set a) : Set a where
  field
    ring : Ring A
    inverse : A → A
    nontrivial : Ring.zero ring ≠ Ring.one ring
    inverse-zero :
      inverse (Ring.zero ring) ≡ Ring.zero ring
    inverse-left :
      (x : A) →
      x ≠ Ring.zero ring →
      Ring.multiply ring (inverse x) x ≡ Ring.one ring
    inverse-right :
      (x : A) →
      x ≠ Ring.zero ring →
      Ring.multiply ring x (inverse x) ≡ Ring.one ring

record Algebra
  {b a : Level}
  {Base : Set b}
  {A : Set a}
  (base : CommutativeSemiring Base)
  (ring : Ring A) :
  Set (b ⊔ a) where

  field
    scalar : Base → A
    scalar-zero :
      scalar (CommutativeSemiring.zero base) ≡ Ring.zero ring
    scalar-one :
      scalar (CommutativeSemiring.one base) ≡ Ring.one ring
    scalar-add :
      (r s : Base) →
      scalar (CommutativeSemiring.add base r s) ≡
      Ring.add ring (scalar r) (scalar s)
    scalar-multiply :
      (r s : Base) →
      scalar (CommutativeSemiring.multiply base r s) ≡
      Ring.multiply ring (scalar r) (scalar s)
    scalar-central :
      (r : Base) (x : A) →
      Ring.multiply ring (scalar r) x ≡
      Ring.multiply ring x (scalar r)

record LeftIdeal
  {a : Level}
  {A : Set a}
  (ring : Ring A) :
  Set (lsuc a) where

  field
    member : A → Set a
    membership-propositional :
      (x : A) (p q : member x) → p ≡ q
    contains-zero :
      member (Ring.zero ring)
    closed-add :
      (x y : A) → member x → member y →
      member (Ring.add ring x y)
    closed-negate :
      (x : A) → member x →
      member (Ring.negate ring x)
    closed-left-multiply :
      (r x : A) → member x →
      member (Ring.multiply ring r x)

record DirectComplement
  {a : Level}
  {A : Set a}
  (ring : Ring A)
  (I J : LeftIdeal ring) :
  Set a where

  field
    intersection-zero :
      (x : A) →
      LeftIdeal.member I x →
      LeftIdeal.member J x →
      x ≡ Ring.zero ring
    spans :
      (x : A) →
      Σ A (λ y →
        Σ (LeftIdeal.member I y) (λ _ →
          Σ A (λ z →
            Σ (LeftIdeal.member J z) (λ _ →
              x ≡ Ring.add ring y z))))

record IsSemisimpleRing
  {a : Level}
  {A : Set a}
  (ring : Ring A) :
  Set (lsuc a) where

  field
    complement :
      (I : LeftIdeal ring) →
      Σ (LeftIdeal ring) (λ J → DirectComplement ring I J)

Nonzero : Nat → Set
Nonzero n = n ≠ zeroN

finEqual : {n : Nat} → Fin n → Fin n → Set
finEqual i j = i ≡ j

MatrixProduct :
  {a : Level} {n : Nat} →
  (D : Fin n → Set a) →
  (d : Fin n → Nat) →
  Set a
MatrixProduct D d =
  (i : Fin _) → Fin (d i) → Fin (d i) → D i

zeroMatrixProduct :
  {a : Level} {n : Nat}
  {D : Fin n → Set a}
  {d : Fin n → Nat} →
  (division : (i : Fin n) → DivisionRing (D i)) →
  MatrixProduct D d
zeroMatrixProduct division i row column =
  Ring.zero (DivisionRing.ring (division i))

addMatrixProduct :
  {a : Level} {n : Nat}
  {D : Fin n → Set a}
  {d : Fin n → Nat} →
  (division : (i : Fin n) → DivisionRing (D i)) →
  MatrixProduct D d →
  MatrixProduct D d →
  MatrixProduct D d
addMatrixProduct division X Y i row column =
  Ring.add (DivisionRing.ring (division i))
    (X i row column)
    (Y i row column)

sumFin :
  {a : Level} {A : Set a} →
  Ring A →
  {n : Nat} →
  (Fin n → A) →
  A
sumFin ring {zeroN} term =
  Ring.zero ring
sumFin ring {sucN n} term =
  Ring.add ring
    (term fzero)
    (sumFin ring (λ i → term (fsuc i)))

multiplyMatrixProduct :
  {a : Level} {n : Nat}
  {D : Fin n → Set a}
  {d : Fin n → Nat} →
  (division : (i : Fin n) → DivisionRing (D i)) →
  MatrixProduct D d →
  MatrixProduct D d →
  MatrixProduct D d
multiplyMatrixProduct division X Y i row column =
  sumFin (DivisionRing.ring (division i))
    (λ middle →
      Ring.multiply (DivisionRing.ring (division i))
        (X i row middle)
        (Y i middle column))

diagonal :
  {a : Level} {A : Set a} {n : Nat} →
  Ring A →
  A →
  Fin n →
  Fin n →
  A
diagonal ring x fzero fzero = x
diagonal ring x fzero (fsuc column) = Ring.zero ring
diagonal ring x (fsuc row) fzero = Ring.zero ring
diagonal ring x (fsuc row) (fsuc column) =
  diagonal ring x row column

oneMatrixProduct :
  {a : Level} {n : Nat}
  {D : Fin n → Set a}
  {d : Fin n → Nat} →
  (division : (i : Fin n) → DivisionRing (D i)) →
  MatrixProduct D d
oneMatrixProduct division i =
  diagonal
    (DivisionRing.ring (division i))
    (Ring.one (DivisionRing.ring (division i)))

scalarMatrixProduct :
  {b a : Level}
  {Base : Set b}
  {n : Nat}
  {D : Fin n → Set a}
  {d : Fin n → Nat} →
  (base : CommutativeSemiring Base) →
  (division : (i : Fin n) → DivisionRing (D i)) →
  (algebras :
    (i : Fin n) →
    Algebra base (DivisionRing.ring (division i))) →
  Base →
  MatrixProduct D d
scalarMatrixProduct base division algebras scalar i =
  diagonal
    (DivisionRing.ring (division i))
    (Algebra.scalar (algebras i) scalar)

record MatrixProductAlgebraEquivalence
  {b a : Level}
  {Base : Set b}
  {A : Set a}
  {n : Nat}
  {D : Fin n → Set a}
  {d : Fin n → Nat}
  (base : CommutativeSemiring Base)
  (sourceRing : Ring A)
  (sourceAlgebra : Algebra base sourceRing)
  (division : (i : Fin n) → DivisionRing (D i))
  (targetAlgebras :
    (i : Fin n) →
    Algebra base (DivisionRing.ring (division i))) :
  Set (b ⊔ a) where

  field
    to : A → MatrixProduct D d
    from : MatrixProduct D d → A
    from-to :
      (x : A) → from (to x) ≡ x
    to-from :
      (Y : MatrixProduct D d) →
      (i : Fin n) →
      (row column : Fin (d i)) →
      to (from Y) i row column ≡ Y i row column
    map-zero :
      (i : Fin n) →
      (row column : Fin (d i)) →
      to (Ring.zero sourceRing) i row column ≡
      zeroMatrixProduct {d = d} division i row column
    map-one :
      (i : Fin n) →
      (row column : Fin (d i)) →
      to (Ring.one sourceRing) i row column ≡
      oneMatrixProduct {d = d} division i row column
    map-add :
      (x y : A) →
      (i : Fin n) →
      (row column : Fin (d i)) →
      to (Ring.add sourceRing x y) i row column ≡
      addMatrixProduct division (to x) (to y) i row column
    map-multiply :
      (x y : A) →
      (i : Fin n) →
      (row column : Fin (d i)) →
      to (Ring.multiply sourceRing x y) i row column ≡
      multiplyMatrixProduct division (to x) (to y) i row column
    map-scalar :
      (r : Base) →
      (i : Fin n) →
      (row column : Fin (d i)) →
      to (Algebra.scalar sourceAlgebra r) i row column ≡
      scalarMatrixProduct {d = d}
        base division targetAlgebras r i row column

artin-wedderburn-theorem :
  (b a : Level) →
  Set (lsuc (b ⊔ a))
artin-wedderburn-theorem b a =
  (Base : Set b) →
  (A : Set a) →
  (base : CommutativeSemiring Base) →
  (ring : Ring A) →
  (algebra : Algebra base ring) →
  IsSemisimpleRing ring →
  Σ Nat (λ n →
    Σ (Fin n → Set a) (λ D →
      Σ (Fin n → Nat) (λ d →
        Σ ((i : Fin n) → DivisionRing (D i)) (λ division →
          Σ ((i : Fin n) →
              Algebra base (DivisionRing.ring (division i)))
            (λ targetAlgebras →
              Σ ((i : Fin n) → Nonzero (d i)) (λ _ →
                MatrixProductAlgebraEquivalence
                  {n = n} {D = D} {d = d}
                  base ring algebra division targetAlgebras))))))
