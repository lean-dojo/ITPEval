-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_a6
-- (putnambench__agda__putnam_2015_a6): determinant equality for intertwined
-- real matrices with the same characteristic polynomial. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

record RingOperations (R : Set) : Set where
  field
    zeroElement oneElement : R
    addElements multiplyElements : R -> R -> R
    negateElement : R -> R

realRingOperations :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RingOperations R
realRingOperations reals =
  record
    { zeroElement = zeroR reals
    ; oneElement = oneR reals
    ; addElements = add reals
    ; multiplyElements = multiply reals
    ; negateElement = negate reals
    }

Polynomial : Set -> Set
Polynomial R =
  List R

polynomialAdd :
  {R : Set} ->
  RingOperations R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
polynomialAdd operations [] q =
  q
polynomialAdd operations p [] =
  p
polynomialAdd operations (x ∷ p) (y ∷ q) =
  RingOperations.addElements operations x y ∷
  polynomialAdd operations p q

polynomialNegate :
  {R : Set} ->
  RingOperations R ->
  Polynomial R ->
  Polynomial R
polynomialNegate operations [] =
  []
polynomialNegate operations (x ∷ p) =
  RingOperations.negateElement operations x ∷
  polynomialNegate operations p

polynomialScale :
  {R : Set} ->
  RingOperations R ->
  R ->
  Polynomial R ->
  Polynomial R
polynomialScale operations scalar [] =
  []
polynomialScale operations scalar (x ∷ p) =
  RingOperations.multiplyElements operations scalar x ∷
  polynomialScale operations scalar p

polynomialMultiply :
  {R : Set} ->
  RingOperations R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
polynomialMultiply operations [] q =
  []
polynomialMultiply operations (x ∷ p) q =
  polynomialAdd operations
    (polynomialScale operations x q)
    (RingOperations.zeroElement operations ∷
      polynomialMultiply operations p q)

polynomialOperations :
  {R : Set} ->
  RingOperations R ->
  RingOperations (Polynomial R)
polynomialOperations operations =
  record
    { zeroElement = []
    ; oneElement = RingOperations.oneElement operations ∷ []
    ; addElements = polynomialAdd operations
    ; multiplyElements = polynomialMultiply operations
    ; negateElement = polynomialNegate operations
    }

constantPolynomial :
  {R : Set} ->
  RingOperations R ->
  R ->
  Polynomial R
constantPolynomial operations x =
  x ∷ []

variablePolynomial :
  {R : Set} ->
  RingOperations R ->
  Polynomial R
variablePolynomial operations =
  RingOperations.zeroElement operations ∷
  RingOperations.oneElement operations ∷
  []

Matrix :
  Set ->
  Nat ->
  Set
Matrix R n =
  Fin n -> Fin n -> R

MatrixEqual :
  {R : Set} {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Set
MatrixEqual {n = n} A B =
  (i j : Fin n) ->
  A i j == B i j

finEqual :
  {n : Nat} ->
  Fin n ->
  Fin n ->
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
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
select true yes no =
  yes
select false yes no =
  no

sumFin :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin operations {zero} term =
  RingOperations.zeroElement operations
sumFin operations {suc n} term =
  RingOperations.addElements operations
    (term fzero)
    (sumFin operations (\ i -> term (fsuc i)))

matrixAdd :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixAdd operations A B i j =
  RingOperations.addElements operations (A i j) (B i j)

matrixNegate :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n
matrixNegate operations A i j =
  RingOperations.negateElement operations (A i j)

matrixSubtract :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixSubtract operations A B =
  matrixAdd operations A (matrixNegate operations B)

matrixMultiply :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix R n ->
  Matrix R n ->
  Matrix R n
matrixMultiply operations A B i j =
  sumFin operations
    (\ k ->
      RingOperations.multiplyElements operations
        (A i k)
        (B k j))

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} removed ()
skip {suc n} fzero i =
  fsuc i
skip {suc n} (fsuc removed) fzero =
  fzero
skip {suc n} (fsuc removed) (fsuc i) =
  fsuc (skip removed i)

firstRowMinor :
  {R : Set} {n : Nat} ->
  Matrix R (suc n) ->
  Fin (suc n) ->
  Matrix R n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

alternatingSign :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Fin n ->
  R
alternatingSign operations fzero =
  RingOperations.oneElement operations
alternatingSign operations (fsuc i) =
  RingOperations.negateElement operations
    (alternatingSign operations i)

determinant :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix R n ->
  R
determinant operations {zero} A =
  RingOperations.oneElement operations
determinant operations {suc n} A =
  sumFin operations
    (\ column ->
      RingOperations.multiplyElements operations
        (alternatingSign operations column)
        (RingOperations.multiplyElements operations
          (A fzero column)
          (determinant operations
            (firstRowMinor A column))))

characteristicMatrix :
  {R : Set} ->
  RingOperations R ->
  {n : Nat} ->
  Matrix R n ->
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
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  Polynomial R
characteristicPolynomial reals A =
  determinant
    (polynomialOperations (realRingOperations reals))
    (characteristicMatrix (realRingOperations reals) A)

putnam-2015-a6 : Set1
putnam-2015-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  (A B M : Matrix R n) ->
  MatrixEqual
    (matrixMultiply (realRingOperations reals) A M)
    (matrixMultiply (realRingOperations reals) M B) ->
  characteristicPolynomial reals A ==
    characteristicPolynomial reals B ->
  (X : Matrix R n) ->
  determinant (realRingOperations reals)
    (matrixSubtract (realRingOperations reals)
      A
      (matrixMultiply (realRingOperations reals) M X)) ==
  determinant (realRingOperations reals)
    (matrixSubtract (realRingOperations reals)
      B
      (matrixMultiply (realRingOperations reals) X M))
