-- Statement-only formalization of PutnamBench corpus artifact putnam_2000_a2:
-- arbitrarily large integers begin three consecutive sums of two integer
-- squares. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<Z_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<Z_ : Int -> Int -> Set where
  negative<positive :
    {m n : Nat} ->
    negsuc m <Z pos n
  positive<positive :
    {m n : Nat} ->
    suc m <=N n ->
    pos m <Z pos n
  negative<negative :
    {m n : Nat} ->
    suc n <=N m ->
    negsuc m <Z negsuc n

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

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

squareInt : Int -> Int
squareInt (pos n) =
  pos (n * n)
squareInt (negsuc n) =
  pos (suc n * suc n)

oneZ : Int
oneZ =
  pos (suc zero)

twoZ : Int
twoZ =
  pos (suc (suc zero))

SumOfTwoSquares : Int -> Set
SumOfTwoSquares n =
  Exists Int
    (\ a ->
      Exists Int
        (\ b ->
          n == addInt (squareInt a) (squareInt b)))

putnam-2000-a2 : Set
putnam-2000-a2 =
  (lower : Int) ->
  Exists Int
    (\ n ->
      (lower <Z n)
      and
      SumOfTwoSquares n
      and
      SumOfTwoSquares (addInt n oneZ)
      and
      SumOfTwoSquares (addInt n twoZ))
