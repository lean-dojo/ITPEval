-- Statement-only formalization of PutnamBench corpus artifact putnam_1986_a4:
-- counting {-1, 0, 1}-valued square integer matrices whose transversal sums
-- are independent of the transversal. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1986A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixl 6 _+Z_
infixl 7 _*Z_
infixr 3 _and_

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

oneZ : Int
oneZ =
  pos 1

twoZ : Int
twoZ =
  pos 2

threeZ : Int
threeZ =
  pos 3

fourZ : Int
fourZ =
  pos 4

minusFourZ : Int
minusFourZ =
  negsuc 3

powerInt : Int -> Nat -> Int
powerInt base zero =
  oneZ
powerInt base (suc exponent) =
  powerInt base exponent *Z base

data AllowedEntry : Int -> Set where
  minus-one-entry : AllowedEntry (negsuc zero)
  zero-entry      : AllowedEntry (pos zero)
  one-entry       : AllowedEntry (pos (suc zero))

Matrix : Nat -> Set
Matrix n =
  Fin n -> Fin n -> Int

MatrixEqual :
  {n : Nat} ->
  Matrix n ->
  Matrix n ->
  Set
MatrixEqual {n} A B =
  (i j : Fin n) ->
  A i j == B i j

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A} f =
  (x y : A) ->
  f x == f y ->
  x == y

Surjective :
  {A B : Set} ->
  (A -> B) ->
  Set
Surjective {A} {B} f =
  (y : B) ->
  Exists A (\ x -> f x == y)

IsPermutation :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  Set
IsPermutation permutation =
  Injective permutation
  and
  Surjective permutation

sumFinInt :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
sumFinInt {zero} term =
  pos zero
sumFinInt {suc n} term =
  term fzero +Z
  sumFinInt (\ i -> term (fsuc i))

HasConstantTransversalSum :
  {n : Nat} ->
  Matrix n ->
  Set
HasConstantTransversalSum {n} A =
  Exists Int
    (\ sum ->
      (permutation : Fin n -> Fin n) ->
      IsPermutation permutation ->
      sumFinInt (\ i -> A i (permutation i)) == sum)

AdmissibleMatrix :
  {n : Nat} ->
  Matrix n ->
  Set
AdmissibleMatrix {n} A =
  ((i j : Fin n) -> AllowedEntry (A i j))
  and
  HasConstantTransversalSum A

record MatrixCount (n count : Nat) : Set where
  field
    enumerate :
      Fin count ->
      Matrix n
    enumerated-admissible :
      (index : Fin count) ->
      AdmissibleMatrix (enumerate index)
    enumeration-complete :
      (A : Matrix n) ->
      AdmissibleMatrix A ->
      Exists (Fin count)
        (\ index -> MatrixEqual A (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin count) ->
      MatrixEqual
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

putnam-1986-a4-formula : Nat -> Int
putnam-1986-a4-formula n =
  powerInt fourZ n +Z
  twoZ *Z powerInt threeZ n +Z
  minusFourZ *Z powerInt twoZ n +Z
  oneZ

FormulaCount : Nat -> Nat -> Set
FormulaCount n count =
  pos count == putnam-1986-a4-formula n

putnam-1986-a4 : Set
putnam-1986-a4 =
  (f : Nat -> Nat) ->
  ((n : Nat) -> MatrixCount n (f n)) ->
  (n : Nat) ->
  Positive n ->
  FormulaCount n (f n)
