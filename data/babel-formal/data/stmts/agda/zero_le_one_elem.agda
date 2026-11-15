-- Statement-only formalization of the Babel-formal topic zero_le_one_elem. This file contains
-- no proof.

module zero_le_one_elem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

record DecidableEqAlt {m : Level} (M : Set m) : Set m where
  field
    decEq : M → M → Bool

record ZeroAlt {a : Level} (A : Set a) : Set a where
  field
    zero : A

record OneAlt {a : Level} (A : Set a) : Set a where
  field
    one : A

record Preorder {a : Level} (A : Set a) : Set (lsuc a) where
  field
    le       : A → A → Set a
    le-refl  : (x : A) → le x x
    le-trans : (x y z : A) → le x y → le y z → le x z

record ZeroLEOneClass
  {a : Level} {A : Set a}
  (Z : ZeroAlt A) (O : OneAlt A) (P : Preorder A) : Set a where
  field
    zero-le-one :
      Preorder.le P (ZeroAlt.zero Z) (OneAlt.one O)
    zero-le-zero :
      Preorder.le P (ZeroAlt.zero Z) (ZeroAlt.zero Z)

record PartialOrder
  {a : Level} {A : Set a} (P : Preorder A) : Set a where
  field
    le-antisym :
      (x y : A) →
      Preorder.le P x y →
      Preorder.le P y x →
      x ≡ y

record _∧_ {p q : Level} (P : Set p) (Q : Set q) : Set (p ⊔ q) where
  field
    left  : P
    right : Q

choose : ∀ {a : Level} {A : Set a} → Bool → A → A → A
choose true  x _ = x
choose false _ y = y

module MatrixStatements
  {m a : Level} {M : Set m} {A : Set a}
  (D : DecidableEqAlt M)
  (Z : ZeroAlt A)
  (O : OneAlt A)
  (P : Preorder A)
  (C : ZeroLEOneClass Z O P) where

  zeroA : A
  zeroA = ZeroAlt.zero Z

  oneA : A
  oneA = OneAlt.one O

  leA : A → A → Set a
  leA = Preorder.le P

  Matrix : Set (m ⊔ a)
  Matrix = M → M → A

  oneMatrix : Matrix
  oneMatrix i j =
    choose (DecidableEqAlt.decEq D i j) oneA zeroA

  zeroMatrix : Matrix
  zeroMatrix _ _ = zeroA

  matrixLe : Matrix → Matrix → Set (m ⊔ a)
  matrixLe X Y = (i j : M) → leA (X i j) (Y i j)

  matrixEq : Matrix → Matrix → Set (m ⊔ a)
  matrixEq X Y = (i j : M) → X i j ≡ Y i j

  zero-le-one-elem : Set (m ⊔ a)
  zero-le-one-elem =
    (i j : M) → leA zeroA (oneMatrix i j)

  zero-le-one-matrix : Set (m ⊔ a)
  zero-le-one-matrix =
    matrixLe zeroMatrix oneMatrix

  matrix-le-refl : Set (m ⊔ a)
  matrix-le-refl =
    (X : Matrix) → matrixLe X X

  matrix-le-trans : Set (m ⊔ a)
  matrix-le-trans =
    (X Y W : Matrix) →
    matrixLe X Y →
    matrixLe Y W →
    matrixLe X W

  matrix-eq-refl : Set (m ⊔ a)
  matrix-eq-refl =
    (X : Matrix) → matrixEq X X

  matrix-eq-sym : Set (m ⊔ a)
  matrix-eq-sym =
    (X Y : Matrix) →
    matrixEq X Y →
    matrixEq Y X

  matrix-eq-trans : Set (m ⊔ a)
  matrix-eq-trans =
    (X Y W : Matrix) →
    matrixEq X Y →
    matrixEq Y W →
    matrixEq X W

  matrix-eq-le : Set (m ⊔ a)
  matrix-eq-le =
    (X Y : Matrix) →
    matrixEq X Y →
    matrixLe X Y ∧ matrixLe Y X

  matrix-le-antisymm : Set (m ⊔ a)
  matrix-le-antisymm =
    PartialOrder P →
    (X Y : Matrix) →
    matrixLe X Y →
    matrixLe Y X →
    matrixEq X Y
