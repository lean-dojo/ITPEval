-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__097, "Cramer's Rule": the determinant-scaled
-- column-replacement vector solves a square linear system, and for a
-- nonsingular matrix gives the solution coordinatewise. This file contains no proof.

module CramersRule where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infix 1 _↔_

data Bottom : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → Bottom

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record CommutativeRing (R : Set) : Set₁ where
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
    add-zero :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) →
      multiplyR x oneR ≡ x
    multiply-zero :
      (x : R) →
      multiplyR x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

record Field (F : Set) : Set₁ where
  field
    ring : CommutativeRing F
    inverse : F → F
    one-not-zero :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    multiply-inverse :
      (x : F) →
      x ≠ CommutativeRing.zeroR ring →
      CommutativeRing.multiplyR ring x (inverse x) ≡
      CommutativeRing.oneR ring

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

finEqual : {n : Nat} → Fin n → Fin n → Bool
finEqual fzero fzero = true
finEqual fzero (fsuc j) = false
finEqual (fsuc i) fzero = false
finEqual (fsuc i) (fsuc j) = finEqual i j

select : {A : Set} → Bool → A → A → A
select true yes no = yes
select false yes no = no

sumFin :
  {R : Set} →
  CommutativeRing R →
  {n : Nat} →
  (Fin n → R) →
  R
sumFin ring {zero} term =
  CommutativeRing.zeroR ring
sumFin ring {suc n} term =
  CommutativeRing.addR ring
    (term fzero)
    (sumFin ring (λ i → term (fsuc i)))

Matrix : Set → Nat → Set
Matrix R n = Fin n → Fin n → R

Vector : Set → Nat → Set
Vector R n = Fin n → R

VectorEqual :
  {R : Set} {n : Nat} →
  Vector R n →
  Vector R n →
  Set
VectorEqual x y = (i : Fin _) → x i ≡ y i

skip :
  {n : Nat} →
  Fin (suc n) →
  Fin n →
  Fin (suc n)
skip {zero} column ()
skip {suc n} fzero k = fsuc k
skip {suc n} (fsuc column) fzero = fzero
skip {suc n} (fsuc column) (fsuc k) =
  fsuc (skip column k)

firstRowMinor :
  {R : Set} {n : Nat} →
  Matrix R (suc n) →
  Fin (suc n) →
  Matrix R n
firstRowMinor A column i j =
  A (fsuc i) (skip column j)

alternatingSign :
  {R : Set} →
  CommutativeRing R →
  {n : Nat} →
  Fin n →
  R
alternatingSign ring fzero =
  CommutativeRing.oneR ring
alternatingSign ring (fsuc i) =
  CommutativeRing.negateR ring
    (alternatingSign ring i)

determinant :
  {R : Set} →
  CommutativeRing R →
  {n : Nat} →
  Matrix R n →
  R
determinant ring {zero} A =
  CommutativeRing.oneR ring
determinant ring {suc n} A =
  sumFin ring
    (λ column →
      CommutativeRing.multiplyR ring
        (alternatingSign ring column)
        (CommutativeRing.multiplyR ring
          (A fzero column)
          (determinant ring (firstRowMinor A column))))

replaceColumn :
  {R : Set} {n : Nat} →
  Matrix R n →
  Fin n →
  Vector R n →
  Matrix R n
replaceColumn A column b i j =
  select (finEqual j column) (b i) (A i j)

cramerVector :
  {R : Set} →
  (ring : CommutativeRing R) →
  {n : Nat} →
  Matrix R n →
  Vector R n →
  Vector R n
cramerVector ring A b i =
  determinant ring (replaceColumn A i b)

matrixVectorProduct :
  {R : Set} →
  (ring : CommutativeRing R) →
  {n : Nat} →
  Matrix R n →
  Vector R n →
  Vector R n
matrixVectorProduct ring A x i =
  sumFin ring
    (λ j →
      CommutativeRing.multiplyR ring (A i j) (x j))

scalarVector :
  {R : Set} →
  (ring : CommutativeRing R) →
  {n : Nat} →
  R →
  Vector R n →
  Vector R n
scalarVector ring scalar x i =
  CommutativeRing.multiplyR ring scalar (x i)

divide :
  {F : Set} →
  Field F →
  F →
  F →
  F
divide fieldStructure numerator denominator =
  CommutativeRing.multiplyR (Field.ring fieldStructure)
    numerator
    (Field.inverse fieldStructure denominator)

cramerSolution :
  {F : Set} →
  (fieldStructure : Field F) →
  {n : Nat} →
  Matrix F n →
  Vector F n →
  Vector F n
cramerSolution fieldStructure A b i =
  divide fieldStructure
    (determinant (Field.ring fieldStructure)
      (replaceColumn A i b))
    (determinant (Field.ring fieldStructure) A)

record CramersRuleStatement : Set₁ where
  field
    determinant-scaled-rule :
      (R : Set) →
      (ring : CommutativeRing R) →
      (n : Nat) →
      (A : Matrix R n) →
      (b : Vector R n) →
      VectorEqual
        (matrixVectorProduct ring A
          (cramerVector ring A b))
        (scalarVector ring
          (determinant ring A)
          b)

    nonsingular-solution-rule :
      (F : Set) →
      (fieldStructure : Field F) →
      (n : Nat) →
      (A : Matrix F n) →
      (x b : Vector F n) →
      determinant (Field.ring fieldStructure) A ≠
        CommutativeRing.zeroR (Field.ring fieldStructure) →
      VectorEqual
        (matrixVectorProduct (Field.ring fieldStructure) A x)
        b
      ↔
      VectorEqual x (cramerSolution fieldStructure A b)

cramers-rule : Set₁
cramers-rule = CramersRuleStatement
