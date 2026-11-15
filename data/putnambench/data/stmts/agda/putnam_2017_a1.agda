-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_a1:
-- the positive integers omitted by the least set closed under square roots
-- and the stated shifted-square operation. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2017A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _divides_
infixl 6 _+Z_
infixl 7 _*Z_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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
  pos (suc zero)

twoZ : Int
twoZ =
  pos (suc (suc zero))

fiveZ : Int
fiveZ =
  pos (suc (suc (suc (suc (suc zero)))))

square : Int -> Int
square n =
  n *Z n

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

_divides_ : Int -> Int -> Set
divisor divides dividend =
  Exists Int
    (\ quotient ->
      dividend == divisor *Z quotient)

IntegerSet : Set1
IntegerSet =
  Int -> Set

Subset : IntegerSet -> IntegerSet -> Set
Subset A B =
  (x : Int) ->
  A x ->
  B x

SetEqual : IntegerSet -> IntegerSet -> Set
SetEqual A B =
  (x : Int) ->
  Iff (A x) (B x)

Qualifying : IntegerSet -> Set
Qualifying S =
  ((n : Int) -> S n -> PositiveInteger n)
  and
  (S twoZ
  and
  (((n : Int) ->
      PositiveInteger n ->
      S (square n) ->
      S n)
  and
  ((n : Int) ->
    S n ->
    S (square (n +Z fiveZ)))))

IsQualifyingDefinition : (IntegerSet -> Set) -> Set1
IsQualifyingDefinition IsQualifying =
  (S : IntegerSet) ->
  Iff (IsQualifying S) (Qualifying S)

record IsLeast
  (property : IntegerSet -> Set)
  (S : IntegerSet) :
  Set1 where

  field
    satisfies :
      property S
    contained-in-every-satisfying-set :
      (T : IntegerSet) ->
      property T ->
      Subset S T

putnam-2017-a1-solution : IntegerSet
putnam-2017-a1-solution x =
  PositiveInteger x
  and
  ((x == oneZ) or (fiveZ divides x))

putnam-2017-a1 : Set1
putnam-2017-a1 =
  (IsQualifying : IntegerSet -> Set) ->
  IsQualifyingDefinition IsQualifying ->
  (S : IntegerSet) ->
  IsLeast IsQualifying S ->
  SetEqual
    (\ x -> Not (S x) and PositiveInteger x)
    putnam-2017-a1-solution
