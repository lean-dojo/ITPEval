-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_b6
-- (putnambench__agda__putnam_2023_b6): the determinant of the matrix counting
-- nonnegative integer solutions to a(i+1) + b(j+1) = n. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

Positive : Nat -> Set
Positive n =
  suc zero <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

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

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

indicator : Bool -> Nat
indicator true =
  suc zero
indicator false =
  zero

countFin :
  {n : Nat} ->
  (Fin n -> Bool) ->
  Nat
countFin {zero} predicate =
  zero
countFin {suc n} predicate =
  indicator (predicate fzero) +
  countFin (\ i -> predicate (fsuc i))

sumFinNat :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFinNat {zero} term =
  zero
sumFinNat {suc n} term =
  term fzero +
  sumFinNat (\ i -> term (fsuc i))

Matrix : Set -> Nat -> Set
Matrix A n =
  Fin n -> Fin n -> A

solutionCount :
  (n : Nat) ->
  Fin n ->
  Fin n ->
  Nat
solutionCount n i j =
  sumFinNat {suc n}
    (\ a ->
      countFin {suc n}
        (\ b ->
          natEqual
            (finToNat a * suc (finToNat i) +
             finToNat b * suc (finToNat j))
            n))

EntriesCountSolutions :
  (n : Nat) ->
  Matrix Int n ->
  Set
EntriesCountSolutions n S =
  (i j : Fin n) ->
  S i j == pos (solutionCount n i j)

sumFinInt :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
sumFinInt {zero} term =
  pos zero
sumFinInt {suc n} term =
  addInt
    (term fzero)
    (sumFinInt (\ i -> term (fsuc i)))

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
  Matrix Int (suc n) ->
  Fin (suc n) ->
  Matrix Int n
firstRowMinor S removedColumn i j =
  S (fsuc i) (skip removedColumn j)

alternatingSign :
  {n : Nat} ->
  Fin n ->
  Int
alternatingSign fzero =
  pos (suc zero)
alternatingSign (fsuc i) =
  negateInt (alternatingSign i)

determinant :
  {n : Nat} ->
  Matrix Int n ->
  Int
determinant {zero} S =
  pos (suc zero)
determinant {suc n} S =
  sumFinInt
    (\ column ->
      multiplyInt
        (alternatingSign column)
        (multiplyInt
          (S fzero column)
          (determinant (firstRowMinor S column))))

ceilingHalf : Nat -> Nat
ceilingHalf zero =
  zero
ceilingHalf (suc zero) =
  suc zero
ceilingHalf (suc (suc n)) =
  suc (ceilingHalf n)

minusOnePower : Nat -> Int
minusOnePower zero =
  pos (suc zero)
minusOnePower (suc exponent) =
  negateInt (minusOnePower exponent)

putnam-2023-b6-solution : Nat -> Int
putnam-2023-b6-solution n =
  multiplyInt
    (minusOnePower (suc (ceilingHalf n)))
    (pos (suc (suc zero) * ceilingHalf n))

putnam-2023-b6 : Set
putnam-2023-b6 =
  (n : Nat) ->
  Positive n ->
  (S : Matrix Int n) ->
  EntriesCountSolutions n S ->
  determinant S == putnam-2023-b6-solution n
