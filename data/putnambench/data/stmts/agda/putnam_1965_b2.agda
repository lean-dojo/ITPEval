-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_b2:
-- in a finite round-robin tournament with more than one player, the sum of
-- squared win counts equals the sum of squared loss counts. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

notBool : Bool -> Bool
notBool false =
  true
notBool true =
  false

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

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

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

indicator : Bool -> Int
indicator false =
  pos zero
indicator true =
  pos (suc zero)

sumFin : {n : Nat} -> (Fin n -> Int) -> Int
sumFin {zero} terms =
  pos zero
sumFin {suc n} terms =
  addInt
    (terms fzero)
    (sumFin (\ i -> terms (fsuc i)))

FunctionEqual :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
FunctionEqual f g =
  (x : _) -> f x == g x

oneN : Nat
oneN =
  suc zero

oneZ : Int
oneZ =
  pos oneN

putnam-1965-b2 : Set
putnam-1965-b2 =
  (n : Nat) ->
  oneN <N n ->
  (won : Fin n -> Fin n -> Bool) ->
  ((i : Fin n) -> won i i == false) ->
  ((i j : Fin n) -> i != j -> won i j == notBool (won j i)) ->
  (w l : Fin n -> Int) ->
  FunctionEqual w
    (\ r ->
      sumFin
        (\ j -> indicator (won r j))) ->
  FunctionEqual l
    (\ r ->
      subtractInt
        (subtractInt (pos n) oneZ)
        (w r)) ->
  sumFin (\ r -> squareInt (w r))
  ==
  sumFin (\ r -> squareInt (l r))
