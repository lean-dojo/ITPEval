-- Statement-only formalization of PutnamBench corpus artifact putnam_1986_b6:
-- a square-matrix identity over an arbitrary field, assuming two products are
-- symmetric and a related difference is the identity. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Field
  {a : Level}
  (F : Set a) :
  Set a where

  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    zero-not-one :
      zeroF != oneF

    add-commutative :
      (x y : F) ->
      add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) ->
      add x zeroF == x
    add-inverse :
      (x : F) ->
      add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : F) ->
      multiply x oneF == x
    distribute :
      (x y z : F) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiply x (inverse x) == oneF

open Field

Matrix :
  {a : Level} ->
  Set a ->
  Nat ->
  Set a
Matrix F n =
  Fin n -> Fin n -> F

MatrixEqual :
  {a : Level} {F : Set a} {n : Nat} ->
  Matrix F n ->
  Matrix F n ->
  Set a
MatrixEqual {n = n} A B =
  (i j : Fin n) ->
  A i j == B i j

sumFin :
  {a : Level} {F : Set a} ->
  Field F ->
  {n : Nat} ->
  (Fin n -> F) ->
  F
sumFin fieldStructure {zero} term =
  zeroF fieldStructure
sumFin fieldStructure {suc n} term =
  add fieldStructure
    (term fzero)
    (sumFin fieldStructure (\ i -> term (fsuc i)))

transpose :
  {a : Level} {F : Set a} {n : Nat} ->
  Matrix F n ->
  Matrix F n
transpose A i j =
  A j i

matrixMultiply :
  {a : Level} {F : Set a} {n : Nat} ->
  Field F ->
  Matrix F n ->
  Matrix F n ->
  Matrix F n
matrixMultiply fieldStructure A B i j =
  sumFin fieldStructure
    (\ k -> multiply fieldStructure (A i k) (B k j))

matrixSubtract :
  {a : Level} {F : Set a} {n : Nat} ->
  Field F ->
  Matrix F n ->
  Matrix F n ->
  Matrix F n
matrixSubtract fieldStructure A B i j =
  add fieldStructure
    (A i j)
    (negate fieldStructure (B i j))

identityMatrix :
  {a : Level} {F : Set a} {n : Nat} ->
  Field F ->
  Matrix F n
identityMatrix fieldStructure fzero fzero =
  oneF fieldStructure
identityMatrix fieldStructure fzero (fsuc j) =
  zeroF fieldStructure
identityMatrix fieldStructure (fsuc i) fzero =
  zeroF fieldStructure
identityMatrix fieldStructure (fsuc i) (fsuc j) =
  identityMatrix fieldStructure i j

Symmetric :
  {a : Level} {F : Set a} {n : Nat} ->
  Matrix F n ->
  Set a
Symmetric A =
  MatrixEqual A (transpose A)

putnam-1986-b6 :
  {a : Level} ->
  Set (lsuc a)
putnam-1986-b6 {a} =
  (n : Nat) ->
  Positive n ->
  (F : Set a) ->
  (fieldStructure : Field F) ->
  (A B C D : Matrix F n) ->
  Symmetric
    (matrixMultiply fieldStructure A (transpose B)) ->
  Symmetric
    (matrixMultiply fieldStructure C (transpose D)) ->
  MatrixEqual
    (matrixSubtract fieldStructure
      (matrixMultiply fieldStructure A (transpose D))
      (matrixMultiply fieldStructure B (transpose C)))
    (identityMatrix fieldStructure) ->
  MatrixEqual
    (matrixSubtract fieldStructure
      (matrixMultiply fieldStructure (transpose A) D)
      (matrixMultiply fieldStructure (transpose C) B))
    (identityMatrix fieldStructure)
