-- Statement-only formalization of Thousand Theorems corpus artifact Q656772,
-- "Cayley–Hamilton theorem": every square matrix over a commutative ring, indexed
-- by an arbitrary finite type, is annihilated by its characteristic polynomial.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q656772_cayley_hamilton_theorem where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record FiniteIndex
  {i : Level}
  (I : Set i) :
  Set (lsuc i) where

  field
    size : Nat
    toFin : I → Fin size
    fromFin : Fin size → I
    to-from :
      (k : Fin size) →
      toFin (fromFin k) ≡ k
    from-to :
      (x : I) →
      fromFin (toFin x) ≡ x

open FiniteIndex

record RingOperations
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

open RingOperations

record CommutativeRing
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    operations : RingOperations R

    add-commutative :
      (x y : R) →
      addR operations x y ≡ addR operations y x
    add-associative :
      (x y z : R) →
      addR operations (addR operations x y) z ≡
      addR operations x (addR operations y z)
    add-zero :
      (x : R) →
      addR operations x (zeroR operations) ≡ x
    add-inverse :
      (x : R) →
      addR operations x (negateR operations x) ≡
      zeroR operations

    multiply-commutative :
      (x y : R) →
      multiplyR operations x y ≡ multiplyR operations y x
    multiply-associative :
      (x y z : R) →
      multiplyR operations (multiplyR operations x y) z ≡
      multiplyR operations x (multiplyR operations y z)
    multiply-one :
      (x : R) →
      multiplyR operations x (oneR operations) ≡ x
    distribute :
      (x y z : R) →
      multiplyR operations x (addR operations y z) ≡
      addR operations
        (multiplyR operations x y)
        (multiplyR operations x z)

open CommutativeRing

Polynomial :
  {r : Level} →
  Set r →
  Set r
Polynomial R =
  List R

polynomialAdd :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  Polynomial R →
  Polynomial R →
  Polynomial R
polynomialAdd operations [] q =
  q
polynomialAdd operations p [] =
  p
polynomialAdd operations (x ∷ p) (y ∷ q) =
  addR operations x y ∷ polynomialAdd operations p q

polynomialNegate :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  Polynomial R →
  Polynomial R
polynomialNegate operations [] =
  []
polynomialNegate operations (x ∷ p) =
  negateR operations x ∷ polynomialNegate operations p

polynomialScale :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  R →
  Polynomial R →
  Polynomial R
polynomialScale operations scalar [] =
  []
polynomialScale operations scalar (x ∷ p) =
  multiplyR operations scalar x ∷
  polynomialScale operations scalar p

polynomialMultiply :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  Polynomial R →
  Polynomial R →
  Polynomial R
polynomialMultiply operations [] q =
  []
polynomialMultiply operations (x ∷ p) q =
  polynomialAdd operations
    (polynomialScale operations x q)
    (zeroR operations ∷ polynomialMultiply operations p q)

polynomialOperations :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  RingOperations (Polynomial R)
polynomialOperations operations =
  record
    { zeroR = []
    ; oneR = oneR operations ∷ []
    ; addR = polynomialAdd operations
    ; multiplyR = polynomialMultiply operations
    ; negateR = polynomialNegate operations
    }

constantPolynomial :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  R →
  Polynomial R
constantPolynomial operations x =
  x ∷ []

variablePolynomial :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  Polynomial R
variablePolynomial operations =
  zeroR operations ∷ oneR operations ∷ []

Matrix :
  {i r : Level} →
  Set i →
  Set r →
  Set (i ⊔ r)
Matrix I R =
  I → I → R

MatrixEqual :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  Matrix I R →
  Matrix I R →
  Set (i ⊔ r)
MatrixEqual {I = I} A B =
  (row column : I) →
  A row column ≡ B row column

finEqual :
  {n : Nat} →
  Fin n →
  Fin n →
  Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

select :
  {a : Level} →
  {A : Set a} →
  Bool →
  A →
  A →
  A
select true yes no =
  yes
select false yes no =
  no

sumFin :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  {n : Nat} →
  (Fin n → R) →
  R
sumFin operations {zero} term =
  zeroR operations
sumFin operations {suc n} term =
  addR operations
    (term fzero)
    (sumFin operations (λ k → term (fsuc k)))

sumIndex :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  FiniteIndex I →
  RingOperations R →
  (I → R) →
  R
sumIndex finite operations term =
  sumFin operations (λ k → term (fromFin finite k))

zeroMatrix :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  RingOperations R →
  Matrix I R
zeroMatrix operations row column =
  zeroR operations

scalarMatrix :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  FiniteIndex I →
  RingOperations R →
  R →
  Matrix I R
scalarMatrix finite operations scalar row column =
  select
    (finEqual (toFin finite row) (toFin finite column))
    scalar
    (zeroR operations)

matrixAdd :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  RingOperations R →
  Matrix I R →
  Matrix I R →
  Matrix I R
matrixAdd operations A B row column =
  addR operations (A row column) (B row column)

matrixMultiply :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  FiniteIndex I →
  RingOperations R →
  Matrix I R →
  Matrix I R →
  Matrix I R
matrixMultiply finite operations A B row column =
  sumIndex finite operations
    (λ k → multiplyR operations (A row k) (B k column))

reindexMatrix :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  (finite : FiniteIndex I) →
  Matrix I R →
  Matrix (Fin (size finite)) R
reindexMatrix finite A row column =
  A (fromFin finite row) (fromFin finite column)

skip :
  {n : Nat} →
  Fin (suc n) →
  Fin n →
  Fin (suc n)
skip {zero} column ()
skip {suc n} fzero k =
  fsuc k
skip {suc n} (fsuc column) fzero =
  fzero
skip {suc n} (fsuc column) (fsuc k) =
  fsuc (skip column k)

firstRowMinor :
  {r : Level} →
  {R : Set r} →
  {n : Nat} →
  Matrix (Fin (suc n)) R →
  Fin (suc n) →
  Matrix (Fin n) R
firstRowMinor A column row minor-column =
  A (fsuc row) (skip column minor-column)

alternatingSign :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  {n : Nat} →
  Fin n →
  R
alternatingSign operations fzero =
  oneR operations
alternatingSign operations (fsuc i) =
  negateR operations (alternatingSign operations i)

determinant :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  {n : Nat} →
  Matrix (Fin n) R →
  R
determinant operations {zero} A =
  oneR operations
determinant operations {suc n} A =
  sumFin operations
    (λ column →
      multiplyR operations
        (alternatingSign operations column)
        (multiplyR operations
          (A fzero column)
          (determinant operations (firstRowMinor A column))))

characteristicMatrix :
  {r : Level} →
  {R : Set r} →
  RingOperations R →
  {n : Nat} →
  Matrix (Fin n) R →
  Matrix (Fin n) (Polynomial R)
characteristicMatrix operations A row column =
  select (finEqual row column)
    (polynomialAdd operations
      (variablePolynomial operations)
      (polynomialNegate operations
        (constantPolynomial operations (A row column))))
    (polynomialNegate operations
      (constantPolynomial operations (A row column)))

characteristicPolynomial :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  CommutativeRing R →
  (finite : FiniteIndex I) →
  Matrix I R →
  Polynomial R
characteristicPolynomial ring finite A =
  determinant
    (polynomialOperations (operations ring))
    (characteristicMatrix
      (operations ring)
      (reindexMatrix finite A))

evaluateAtMatrix :
  {i r : Level} →
  {I : Set i} →
  {R : Set r} →
  FiniteIndex I →
  RingOperations R →
  Polynomial R →
  Matrix I R →
  Matrix I R
evaluateAtMatrix finite operations [] A =
  zeroMatrix operations
evaluateAtMatrix finite operations (coefficient ∷ coefficients) A =
  matrixAdd operations
    (scalarMatrix finite operations coefficient)
    (matrixMultiply finite operations A
      (evaluateAtMatrix finite operations coefficients A))

cayley-hamilton-theorem : Setω
cayley-hamilton-theorem =
  {i r : Level} →
  (I : Set i) →
  (finite : FiniteIndex I) →
  (R : Set r) →
  (ring : CommutativeRing R) →
  (A : Matrix I R) →
  MatrixEqual
    (evaluateAtMatrix finite
      (operations ring)
      (characteristicPolynomial ring finite A)
      A)
    (zeroMatrix (operations ring))
