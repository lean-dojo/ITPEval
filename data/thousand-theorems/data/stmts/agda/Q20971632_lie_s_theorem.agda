-- Statement-only formalization of Thousand Theorems corpus artifact Q20971632,
-- "Lie's theorem": a finite nontrivial triangularizable module over a solvable Lie
-- algebra in characteristic zero has a nonzero common weight vector. This file contains no proof.

{-# OPTIONS --safe #-}

module Q20971632_lie_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
  renaming (zero to zeroN; suc to sucN)
open import Agda.Builtin.Sigma using (Σ)

data Empty : Set where

Not :
  {a : Level} →
  Set a →
  Set a
Not A = A → Empty

infix 4 _≠_
infixr 3 _∧_

_≠_ :
  {a : Level} {A : Set a} →
  A →
  A →
  Set a
x ≠ y = Not (x ≡ y)

record _∧_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    left  : A
    right : B

data Truth {a : Level} : Set a where
  truth : Truth

record Field
  {k : Level}
  (K : Set k) :
  Set k where

  field
    zero one : K
    add multiply : K → K → K
    negate inverse : K → K

    add-associative :
      (x y z : K) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : K) →
      add x y ≡ add y x
    add-zero-left :
      (x : K) →
      add zero x ≡ x
    add-zero-right :
      (x : K) →
      add x zero ≡ x
    add-inverse-left :
      (x : K) →
      add (negate x) x ≡ zero
    add-inverse-right :
      (x : K) →
      add x (negate x) ≡ zero

    multiply-associative :
      (x y z : K) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-commutative :
      (x y : K) →
      multiply x y ≡ multiply y x
    multiply-one-left :
      (x : K) →
      multiply one x ≡ x
    multiply-one-right :
      (x : K) →
      multiply x one ≡ x
    multiply-zero-left :
      (x : K) →
      multiply zero x ≡ zero
    multiply-zero-right :
      (x : K) →
      multiply x zero ≡ zero

    distribute-left :
      (x y z : K) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : K) →
      multiply (add x y) z ≡
      add (multiply x z) (multiply y z)

    zero-not-one :
      zero ≠ one
    inverse-zero :
      inverse zero ≡ zero
    inverse-left :
      (x : K) →
      x ≠ zero →
      multiply (inverse x) x ≡ one
    inverse-right :
      (x : K) →
      x ≠ zero →
      multiply x (inverse x) ≡ one

natCast :
  {k : Level} {K : Set k} →
  Field K →
  Nat →
  K
natCast scalarField zeroN =
  Field.zero scalarField
natCast scalarField (sucN n) =
  Field.add scalarField (natCast scalarField n) (Field.one scalarField)

record CharacteristicZero
  {k : Level} {K : Set k}
  (scalarField : Field K) :
  Set k where

  field
    nat-injective :
      (m n : Nat) →
      natCast scalarField m ≡ natCast scalarField n →
      m ≡ n

record AdditiveCommutativeGroup
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

record VectorSpace
  {k a : Level}
  {K : Set k}
  (scalarField : Field K)
  (A : Set a) :
  Set (k ⊔ a) where

  field
    additive : AdditiveCommutativeGroup A
    smul : K → A → A

    one-smul :
      (x : A) →
      smul (Field.one scalarField) x ≡ x
    multiply-smul :
      (r s : K) (x : A) →
      smul (Field.multiply scalarField r s) x ≡ smul r (smul s x)
    add-smul :
      (r s : K) (x : A) →
      smul (Field.add scalarField r s) x ≡
      AdditiveCommutativeGroup.add additive (smul r x) (smul s x)
    smul-add :
      (r : K) (x y : A) →
      smul r (AdditiveCommutativeGroup.add additive x y) ≡
      AdditiveCommutativeGroup.add additive (smul r x) (smul r y)
    zero-smul :
      (x : A) →
      smul (Field.zero scalarField) x ≡ AdditiveCommutativeGroup.zero additive
    smul-zero :
      (r : K) →
      smul r (AdditiveCommutativeGroup.zero additive) ≡
      AdditiveCommutativeGroup.zero additive

zeroOf :
  {k a : Level} {K : Set k} {scalarField : Field K} {A : Set a} →
  VectorSpace scalarField A →
  A
zeroOf space =
  AdditiveCommutativeGroup.zero (VectorSpace.additive space)

addOf :
  {k a : Level} {K : Set k} {scalarField : Field K} {A : Set a} →
  VectorSpace scalarField A →
  A →
  A →
  A
addOf space =
  AdditiveCommutativeGroup.add (VectorSpace.additive space)

negateOf :
  {k a : Level} {K : Set k} {scalarField : Field K} {A : Set a} →
  VectorSpace scalarField A →
  A →
  A
negateOf space =
  AdditiveCommutativeGroup.negate (VectorSpace.additive space)

smulOf :
  {k a : Level} {K : Set k} {scalarField : Field K} {A : Set a} →
  VectorSpace scalarField A →
  K →
  A →
  A
smulOf =
  VectorSpace.smul

record LieAlgebra
  {k l : Level}
  {K : Set k}
  (scalarField : Field K)
  (L : Set l) :
  Set (k ⊔ l) where

  field
    space : VectorSpace scalarField L
    bracket : L → L → L

    bracket-add-left :
      (x y z : L) →
      bracket (addOf space x y) z ≡
      addOf space (bracket x z) (bracket y z)
    bracket-add-right :
      (x y z : L) →
      bracket x (addOf space y z) ≡
      addOf space (bracket x y) (bracket x z)
    bracket-self :
      (x : L) →
      bracket x x ≡ zeroOf space
    leibniz-jacobi :
      (x y z : L) →
      bracket x (bracket y z) ≡
      addOf space (bracket (bracket x y) z) (bracket y (bracket x z))
    bracket-smul-right :
      (r : K) (x y : L) →
      bracket x (smulOf space r y) ≡ smulOf space r (bracket x y)

record LieRepresentation
  {k l v : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  (algebra : LieAlgebra scalarField L)
  (V : Set v) :
  Set (k ⊔ l ⊔ v) where

  field
    space : VectorSpace scalarField V
    action : L → V → V

    action-add-left :
      (x y : L) (w : V) →
      action (addOf (LieAlgebra.space algebra) x y) w ≡
      addOf space (action x w) (action y w)
    action-add-right :
      (x : L) (u w : V) →
      action x (addOf space u w) ≡
      addOf space (action x u) (action x w)
    action-leibniz :
      (x y : L) (w : V) →
      action x (action y w) ≡
      addOf space
        (action (LieAlgebra.bracket algebra x y) w)
        (action y (action x w))
    action-smul-left :
      (r : K) (x : L) (w : V) →
      action (smulOf (LieAlgebra.space algebra) r x) w ≡
      smulOf space r (action x w)
    action-smul-right :
      (r : K) (x : L) (w : V) →
      action x (smulOf space r w) ≡
      smulOf space r (action x w)

record LinearFunctional
  {k l : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  (space : VectorSpace scalarField L) :
  Set (k ⊔ l) where

  field
    apply : L → K
    map-add :
      (x y : L) →
      apply (addOf space x y) ≡ Field.add scalarField (apply x) (apply y)
    map-smul :
      (r : K) (x : L) →
      apply (smulOf space r x) ≡ Field.multiply scalarField r (apply x)

data Fin : Nat → Set where
  first : {n : Nat} → Fin (sucN n)
  next  : {n : Nat} → Fin n → Fin (sucN n)

data InSpan
  {k a : Level}
  {K : Set k}
  {scalarField : Field K}
  {A : Set a}
  (space : VectorSpace scalarField A)
  {n : Nat}
  (generators : Fin n → A) :
  A →
  Set (k ⊔ a) where

  span-generator :
    (i : Fin n) →
    InSpan space generators (generators i)
  span-zero :
    InSpan space generators (zeroOf space)
  span-add :
    {x y : A} →
    InSpan space generators x →
    InSpan space generators y →
    InSpan space generators (addOf space x y)
  span-negate :
    {x : A} →
    InSpan space generators x →
    InSpan space generators (negateOf space x)
  span-smul :
    (r : K) {x : A} →
    InSpan space generators x →
    InSpan space generators (smulOf space r x)

FiniteGenerated :
  {k a : Level}
  {K : Set k}
  {scalarField : Field K}
  {A : Set a} →
  VectorSpace scalarField A →
  Set (k ⊔ a)
FiniteGenerated {A = A} space =
  Σ Nat (λ n →
    Σ (Fin n → A) (λ generators →
      (x : A) → InSpan space generators x))

NontrivialSpace :
  {k a : Level}
  {K : Set k}
  {scalarField : Field K}
  {A : Set a} →
  VectorSpace scalarField A →
  Set a
NontrivialSpace {A = A} space =
  Σ A (λ x → x ≠ zeroOf space)

data DerivedStep
  {k l : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  (algebra : LieAlgebra scalarField L)
  (P : L → Set (k ⊔ l)) :
  L →
  Set (k ⊔ l) where

  derived-bracket :
    {x y : L} →
    P x →
    P y →
    DerivedStep algebra P (LieAlgebra.bracket algebra x y)
  derived-zero :
    DerivedStep algebra P (zeroOf (LieAlgebra.space algebra))
  derived-add :
    {x y : L} →
    DerivedStep algebra P x →
    DerivedStep algebra P y →
    DerivedStep algebra P (addOf (LieAlgebra.space algebra) x y)
  derived-negate :
    {x : L} →
    DerivedStep algebra P x →
    DerivedStep algebra P (negateOf (LieAlgebra.space algebra) x)
  derived-smul :
    (r : K) {x : L} →
    DerivedStep algebra P x →
    DerivedStep algebra P (smulOf (LieAlgebra.space algebra) r x)

Derived :
  {k l : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l} →
  LieAlgebra scalarField L →
  Nat →
  L →
  Set (k ⊔ l)
Derived algebra zeroN x =
  Truth
Derived algebra (sucN n) x =
  DerivedStep algebra (Derived algebra n) x

IsSolvable :
  {k l : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l} →
  LieAlgebra scalarField L →
  Set (k ⊔ l)
IsSolvable {L = L} algebra =
  Σ Nat (λ n →
    (x : L) →
    Derived algebra n x →
    x ≡ zeroOf (LieAlgebra.space algebra))

shiftedAction :
  {k l v : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  {V : Set v}
  {algebra : LieAlgebra scalarField L} →
  LieRepresentation algebra V →
  L →
  K →
  V →
  V
shiftedAction representation x scalar w =
  addOf (LieRepresentation.space representation)
    (LieRepresentation.action representation x w)
    (negateOf (LieRepresentation.space representation)
      (smulOf (LieRepresentation.space representation) scalar w))

iterateShift :
  {k l v : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  {V : Set v}
  {algebra : LieAlgebra scalarField L} →
  LieRepresentation algebra V →
  L →
  K →
  Nat →
  V →
  V
iterateShift representation x scalar zeroN w =
  w
iterateShift representation x scalar (sucN n) w =
  shiftedAction representation x scalar
    (iterateShift representation x scalar n w)

GeneralizedEigenvector :
  {k l v : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  {V : Set v}
  {algebra : LieAlgebra scalarField L} →
  (representation : LieRepresentation algebra V) →
  L →
  K →
  V →
  Set v
GeneralizedEigenvector representation x scalar w =
  Σ Nat (λ n →
    iterateShift representation x scalar n w ≡
    zeroOf (LieRepresentation.space representation))

data InGeneralizedEigenspaceSpan
  {k l v : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  {V : Set v}
  {algebra : LieAlgebra scalarField L}
  (representation : LieRepresentation algebra V)
  (x : L) :
  V →
  Set (k ⊔ l ⊔ v) where

  generalized-vector :
    (scalar : K) (w : V) →
    GeneralizedEigenvector representation x scalar w →
    InGeneralizedEigenspaceSpan representation x w
  generalized-span-zero :
    InGeneralizedEigenspaceSpan representation x
      (zeroOf (LieRepresentation.space representation))
  generalized-span-add :
    {u w : V} →
    InGeneralizedEigenspaceSpan representation x u →
    InGeneralizedEigenspaceSpan representation x w →
    InGeneralizedEigenspaceSpan representation x
      (addOf (LieRepresentation.space representation) u w)
  generalized-span-negate :
    {w : V} →
    InGeneralizedEigenspaceSpan representation x w →
    InGeneralizedEigenspaceSpan representation x
      (negateOf (LieRepresentation.space representation) w)
  generalized-span-smul :
    (r : K) {w : V} →
    InGeneralizedEigenspaceSpan representation x w →
    InGeneralizedEigenspaceSpan representation x
      (smulOf (LieRepresentation.space representation) r w)

IsTriangularizable :
  {k l v : Level}
  {K : Set k}
  {scalarField : Field K}
  {L : Set l}
  {V : Set v}
  {algebra : LieAlgebra scalarField L} →
  LieRepresentation algebra V →
  Set (k ⊔ l ⊔ v)
IsTriangularizable {L = L} {V = V} representation =
  (x : L) →
  (w : V) →
  InGeneralizedEigenspaceSpan representation x w

lies-theorem :
  (k l v : Level) →
  Set (lsuc (k ⊔ l ⊔ v))
lies-theorem k l v =
  (K : Set k) →
  (scalarField : Field K) →
  CharacteristicZero scalarField →
  (L : Set l) →
  (algebra : LieAlgebra scalarField L) →
  (V : Set v) →
  (representation : LieRepresentation algebra V) →
  FiniteGenerated (LieRepresentation.space representation) →
  NontrivialSpace (LieRepresentation.space representation) →
  IsSolvable algebra →
  IsTriangularizable representation →
  Σ (LinearFunctional (LieAlgebra.space algebra)) (λ weight →
    Σ V (λ w →
      (w ≠ zeroOf (LieRepresentation.space representation)) ∧
      ((x : L) →
        LieRepresentation.action representation x w ≡
        smulOf (LieRepresentation.space representation)
          (LinearFunctional.apply weight x) w)))
