-- Statement-only formalization of PutnamBench corpus artifact putnam_1994_a4:
-- integer 2 by 2 matrices A, A+B, ..., A+4B having integer matrix inverses
-- imply that A+5B also has an integer matrix inverse. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

data Fin2 : Set where
  i0 i1 : Fin2

Matrix : Set
Matrix =
  Fin2 -> Fin2 -> Int

MatrixEqual : Matrix -> Matrix -> Set
MatrixEqual A B =
  (i j : Fin2) ->
  A i j == B i j

matrixAdd : Matrix -> Matrix -> Matrix
matrixAdd A B i j =
  addInt (A i j) (B i j)

scaleMatrix : Int -> Matrix -> Matrix
scaleMatrix scalar A i j =
  multiplyInt scalar (A i j)

matrixMultiply : Matrix -> Matrix -> Matrix
matrixMultiply A B i j =
  addInt
    (multiplyInt (A i i0) (B i0 j))
    (multiplyInt (A i i1) (B i1 j))

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

identityMatrix : Matrix
identityMatrix i0 i0 =
  pos oneN
identityMatrix i0 i1 =
  pos zero
identityMatrix i1 i0 =
  pos zero
identityMatrix i1 i1 =
  pos oneN

Invertible : Matrix -> Set
Invertible A =
  Exists Matrix
    (\ AInverse ->
      MatrixEqual
        (matrixMultiply A AInverse)
        identityMatrix
      and
      MatrixEqual
        (matrixMultiply AInverse A)
        identityMatrix)

affineMatrix : Matrix -> Matrix -> Nat -> Matrix
affineMatrix A B coefficient =
  matrixAdd A (scaleMatrix (pos coefficient) B)

putnam-1994-a4 : Set
putnam-1994-a4 =
  (A B : Matrix) ->
  Invertible A
  and
  Invertible (affineMatrix A B oneN)
  and
  Invertible (affineMatrix A B twoN)
  and
  Invertible (affineMatrix A B threeN)
  and
  Invertible (affineMatrix A B fourN) ->
  Invertible (affineMatrix A B fiveN)
