-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_b5
-- (putnambench__agda__putnam_2021_b5): positive powers of an integer matrix
-- preserve odd determinants of all nonempty principal submatrices. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixl 6 _+Z_
infixl 7 _*Z_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

zeroZ : Int
zeroZ =
  pos zero

oneZ : Int
oneZ =
  pos (suc zero)

twoZ : Int
twoZ =
  pos (suc (suc zero))

negateZ : Int -> Int
negateZ (pos zero) =
  pos zero
negateZ (pos (suc n)) =
  negsuc n
negateZ (negsuc n) =
  pos (suc n)

OddInt : Int -> Set
OddInt z =
  Exists Int
    (\ half -> z == (twoZ *Z half) +Z oneZ)

finEqual : {n : Nat} -> Fin n -> Fin n -> Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

select : {A : Set} -> Bool -> A -> A -> A
select true yes no =
  yes
select false yes no =
  no

Matrix : Nat -> Set
Matrix n =
  Fin n -> Fin n -> Int

identityMatrix : {n : Nat} -> Matrix n
identityMatrix i j =
  select (finEqual i j) oneZ zeroZ

sumFinInt :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
sumFinInt {zero} terms =
  zeroZ
sumFinInt {suc n} terms =
  terms fzero +Z
  sumFinInt (\ i -> terms (fsuc i))

matrixMultiply :
  {n : Nat} ->
  Matrix n ->
  Matrix n ->
  Matrix n
matrixMultiply A B i j =
  sumFinInt
    (\ k -> A i k *Z B k j)

matrixPower :
  {n : Nat} ->
  Matrix n ->
  Nat ->
  Matrix n
matrixPower A zero =
  identityMatrix
matrixPower A (suc k) =
  matrixMultiply (matrixPower A k) A

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
  {n : Nat} ->
  Matrix (suc n) ->
  Fin (suc n) ->
  Matrix n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

alternatingSign : {n : Nat} -> Fin n -> Int
alternatingSign fzero =
  oneZ
alternatingSign (fsuc i) =
  negateZ (alternatingSign i)

determinant :
  {n : Nat} ->
  Matrix n ->
  Int
determinant {zero} A =
  oneZ
determinant {suc n} A =
  sumFinInt
    (\ column ->
      alternatingSign column *Z
      (A fzero column *Z
       determinant (firstRowMinor A column)))

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A} f =
  (x y : A) ->
  f x == f y ->
  x == y

principalSubmatrix :
  {n m : Nat} ->
  Matrix n ->
  (Fin m -> Fin n) ->
  Matrix m
principalSubmatrix A reindex i j =
  A (reindex i) (reindex j)

VeryOdd :
  {n : Nat} ->
  Matrix n ->
  Set
VeryOdd {n} A =
  (m : Nat) ->
  Positive m ->
  m <=N n ->
  (reindex : Fin m -> Fin n) ->
  Injective reindex ->
  OddInt (determinant (principalSubmatrix A reindex))

putnam-2021-b5 : Set
putnam-2021-b5 =
  (n : Nat) ->
  Positive n ->
  (A : Matrix n) ->
  VeryOdd A ->
  (k : Nat) ->
  Positive k ->
  VeryOdd (matrixPower A k)
