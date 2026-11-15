-- Statement-only formalization of PutnamBench corpus artifact putnam_1994_b4
-- (putnambench__agda__putnam_1994_b4): the greatest common divisor of the
-- entries of A^n - I for A = [[3,2],[4,3]] tends to infinity. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=N_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

absInt : Int -> Nat
absInt (pos n) =
  n
absInt (negsuc n) =
  suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b =
  a
gcdWithFuel (suc fuel) a zero =
  a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat -> Nat -> Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

data Fin2 : Set where
  i0 i1 : Fin2

Matrix : Set
Matrix =
  Fin2 -> Fin2 -> Int

matrixMultiply : Matrix -> Matrix -> Matrix
matrixMultiply A B i j =
  addInt
    (multiplyInt (A i i0) (B i0 j))
    (multiplyInt (A i i1) (B i1 j))

matrixSubtract : Matrix -> Matrix -> Matrix
matrixSubtract A B i j =
  subtractInt (A i j) (B i j)

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

identityMatrix : Matrix
identityMatrix i0 i0 =
  pos oneN
identityMatrix i0 i1 =
  pos zero
identityMatrix i1 i0 =
  pos zero
identityMatrix i1 i1 =
  pos oneN

putnamMatrix : Matrix
putnamMatrix i0 i0 =
  pos threeN
putnamMatrix i0 i1 =
  pos twoN
putnamMatrix i1 i0 =
  pos fourN
putnamMatrix i1 i1 =
  pos threeN

matrixPower : Matrix -> Nat -> Matrix
matrixPower A zero =
  identityMatrix
matrixPower A (suc n) =
  matrixMultiply (matrixPower A n) A

gcdEntries : Matrix -> Nat
gcdEntries M =
  naturalGCD
    (naturalGCD
      (naturalGCD
        (absInt (M i0 i0))
        (absInt (M i0 i1)))
      (absInt (M i1 i0)))
    (absInt (M i1 i1))

d : Nat -> Nat
d n =
  gcdEntries
    (matrixSubtract
      (matrixPower putnamMatrix n)
      identityMatrix)

putnam-1994-b4 : Set
putnam-1994-b4 =
  (lowerBound : Nat) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lowerBound <=N d n)
