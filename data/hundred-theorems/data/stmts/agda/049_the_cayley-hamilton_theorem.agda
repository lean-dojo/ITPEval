-- Statement-only formalization of "The Cayley-Hamilton Theorem" from Hundred Theorems item
-- 049: every finite square matrix over a commutative ring is annihilated by its characteristic
-- polynomial. This file contains no proof.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
  renaming (zero to zeroN; suc to sucN)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (sucN n)
  fsuc : {n : Nat} → Fin n → Fin (sucN n)

record RingOperations (R : Set) : Set where
  field
    zero one : R
    add multiply : R → R → R
    negate : R → R

record CommutativeRing (R : Set) : Set where
  field
    operations : RingOperations R

    add-commutative :
      (x y : R) →
      RingOperations.add operations x y ≡
      RingOperations.add operations y x
    add-associative :
      (x y z : R) →
      RingOperations.add operations
        (RingOperations.add operations x y) z ≡
      RingOperations.add operations x
        (RingOperations.add operations y z)
    add-zero :
      (x : R) →
      RingOperations.add operations x
        (RingOperations.zero operations) ≡ x
    add-inverse :
      (x : R) →
      RingOperations.add operations x
        (RingOperations.negate operations x) ≡
      RingOperations.zero operations

    multiply-commutative :
      (x y : R) →
      RingOperations.multiply operations x y ≡
      RingOperations.multiply operations y x
    multiply-associative :
      (x y z : R) →
      RingOperations.multiply operations
        (RingOperations.multiply operations x y) z ≡
      RingOperations.multiply operations x
        (RingOperations.multiply operations y z)
    multiply-one :
      (x : R) →
      RingOperations.multiply operations x
        (RingOperations.one operations) ≡ x
    distribute :
      (x y z : R) →
      RingOperations.multiply operations x
        (RingOperations.add operations y z) ≡
      RingOperations.add operations
        (RingOperations.multiply operations x y)
        (RingOperations.multiply operations x z)

Polynomial : Set → Set
Polynomial R = List R

polynomialAdd :
  {R : Set} →
  RingOperations R →
  Polynomial R →
  Polynomial R →
  Polynomial R
polynomialAdd operations [] q = q
polynomialAdd operations p [] = p
polynomialAdd operations (x ∷ p) (y ∷ q) =
  RingOperations.add operations x y ∷
  polynomialAdd operations p q

polynomialNegate :
  {R : Set} →
  RingOperations R →
  Polynomial R →
  Polynomial R
polynomialNegate operations [] = []
polynomialNegate operations (x ∷ p) =
  RingOperations.negate operations x ∷
  polynomialNegate operations p

polynomialScale :
  {R : Set} →
  RingOperations R →
  R →
  Polynomial R →
  Polynomial R
polynomialScale operations scalar [] = []
polynomialScale operations scalar (x ∷ p) =
  RingOperations.multiply operations scalar x ∷
  polynomialScale operations scalar p

polynomialMultiply :
  {R : Set} →
  RingOperations R →
  Polynomial R →
  Polynomial R →
  Polynomial R
polynomialMultiply operations [] q = []
polynomialMultiply operations (x ∷ p) q =
  polynomialAdd operations
    (polynomialScale operations x q)
    (RingOperations.zero operations ∷
      polynomialMultiply operations p q)

polynomialOperations :
  {R : Set} →
  RingOperations R →
  RingOperations (Polynomial R)
polynomialOperations operations =
  record
    { zero = []
    ; one = RingOperations.one operations ∷ []
    ; add = polynomialAdd operations
    ; multiply = polynomialMultiply operations
    ; negate = polynomialNegate operations
    }

constantPolynomial :
  {R : Set} →
  RingOperations R →
  R →
  Polynomial R
constantPolynomial operations x = x ∷ []

variablePolynomial :
  {R : Set} →
  RingOperations R →
  Polynomial R
variablePolynomial operations =
  RingOperations.zero operations ∷
  RingOperations.one operations ∷
  []

Matrix : Set → Nat → Set
Matrix R n = Fin n → Fin n → R

MatrixEqual :
  {R : Set} {n : Nat} →
  Matrix R n →
  Matrix R n →
  Set
MatrixEqual A B = (i j : Fin _) → A i j ≡ B i j

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
  RingOperations R →
  {n : Nat} →
  (Fin n → R) →
  R
sumFin operations {zeroN} term =
  RingOperations.zero operations
sumFin operations {sucN n} term =
  RingOperations.add operations
    (term fzero)
    (sumFin operations (λ i → term (fsuc i)))

zeroMatrix :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Matrix R n
zeroMatrix operations i j =
  RingOperations.zero operations

scalarMatrix :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  R →
  Matrix R n
scalarMatrix operations scalar i j =
  select (finEqual i j)
    scalar
    (RingOperations.zero operations)

matrixAdd :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Matrix R n →
  Matrix R n →
  Matrix R n
matrixAdd operations A B i j =
  RingOperations.add operations (A i j) (B i j)

matrixMultiply :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Matrix R n →
  Matrix R n →
  Matrix R n
matrixMultiply operations A B i j =
  sumFin operations
    (λ k → RingOperations.multiply operations (A i k) (B k j))

skip :
  {n : Nat} →
  Fin (sucN n) →
  Fin n →
  Fin (sucN n)
skip {zeroN} column ()
skip {sucN n} fzero k = fsuc k
skip {sucN n} (fsuc column) fzero = fzero
skip {sucN n} (fsuc column) (fsuc k) =
  fsuc (skip column k)

firstRowMinor :
  {R : Set} {n : Nat} →
  Matrix R (sucN n) →
  Fin (sucN n) →
  Matrix R n
firstRowMinor A column i j =
  A (fsuc i) (skip column j)

alternatingSign :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Fin n →
  R
alternatingSign operations fzero =
  RingOperations.one operations
alternatingSign operations (fsuc i) =
  RingOperations.negate operations
    (alternatingSign operations i)

determinant :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Matrix R n →
  R
determinant operations {zeroN} A =
  RingOperations.one operations
determinant operations {sucN n} A =
  sumFin operations
    (λ column →
      RingOperations.multiply operations
        (alternatingSign operations column)
        (RingOperations.multiply operations
          (A fzero column)
          (determinant operations (firstRowMinor A column))))

characteristicMatrix :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Matrix R n →
  Matrix (Polynomial R) n
characteristicMatrix operations A i j =
  select (finEqual i j)
    (polynomialAdd operations
      (variablePolynomial operations)
      (polynomialNegate operations
        (constantPolynomial operations (A i j))))
    (polynomialNegate operations
      (constantPolynomial operations (A i j)))

characteristicPolynomial :
  {R : Set} →
  CommutativeRing R →
  {n : Nat} →
  Matrix R n →
  Polynomial R
characteristicPolynomial ring A =
  determinant
    (polynomialOperations (CommutativeRing.operations ring))
    (characteristicMatrix (CommutativeRing.operations ring) A)

evaluateAtMatrix :
  {R : Set} →
  RingOperations R →
  {n : Nat} →
  Polynomial R →
  Matrix R n →
  Matrix R n
evaluateAtMatrix operations [] A =
  zeroMatrix operations
evaluateAtMatrix operations (coefficient ∷ coefficients) A =
  matrixAdd operations
    (scalarMatrix operations coefficient)
    (matrixMultiply operations A
      (evaluateAtMatrix operations coefficients A))

the-cayley-hamilton-theorem : Set₁
the-cayley-hamilton-theorem =
  (R : Set) →
  (ring : CommutativeRing R) →
  (n : Nat) →
  (A : Matrix R n) →
  MatrixEqual
    (evaluateAtMatrix
      (CommutativeRing.operations ring)
      (characteristicPolynomial ring A)
      A)
    (zeroMatrix (CommutativeRing.operations ring))
