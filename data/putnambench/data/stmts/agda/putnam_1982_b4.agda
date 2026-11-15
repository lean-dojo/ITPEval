-- Statement-only formalization of PutnamBench corpus artifact putnam_1982_b4:
-- two claims about finite sets of distinct integers whose element product
-- divides the product after every common additive shift of the elements.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1982B4 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _divides_
infixl 6 _+Z_
infixl 7 _*Z_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
  pos (suc zero)

minusOneZ : Int
minusOneZ =
  negsuc zero

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

record HasCardinality
  (member : Int -> Bool)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Int
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index) == true
    enumeration-complete :
      (x : Int) ->
      member x == true ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record FiniteIntegerSet : Set where
  field
    member :
      Int ->
      Bool
    size :
      Nat
    has-cardinality :
      HasCardinality member size

open HasCardinality
open FiniteIntegerSet

productFin :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
productFin {zero} term =
  oneZ
productFin {suc n} term =
  term fzero *Z productFin (\ index -> term (fsuc index))

setProduct : FiniteIntegerSet -> Int
setProduct finiteSet =
  productFin
    (enumerate (has-cardinality finiteSet))

shiftedSetProduct : FiniteIntegerSet -> Int -> Int
shiftedSetProduct finiteSet shift =
  productFin
    (\ index ->
      enumerate (has-cardinality finiteSet) index +Z shift)

_divides_ : Int -> Int -> Set
divisor divides dividend =
  Exists Int
    (\ quotient ->
      dividend == divisor *Z quotient)

Nonempty : FiniteIntegerSet -> Set
Nonempty finiteSet =
  Exists Int
    (\ x ->
      member finiteSet x == true)

ShiftDivisibility : FiniteIntegerSet -> Set
ShiftDivisibility finiteSet =
  (shift : Int) ->
  setProduct finiteSet divides shiftedSetProduct finiteSet shift

Qualifies : FiniteIntegerSet -> Set
Qualifies finiteSet =
  Nonempty finiteSet
  and
  ShiftDivisibility finiteSet

ContainsUnit : FiniteIntegerSet -> Set
ContainsUnit finiteSet =
  (member finiteSet oneZ == true)
  or
  (member finiteSet minusOneZ == true)

AllPositive : FiniteIntegerSet -> Set
AllPositive finiteSet =
  (x : Int) ->
  member finiteSet x == true ->
  PositiveInteger x

InitialSegment : Nat -> Int -> Set
InitialSegment cardinality (pos zero) =
  Bottom
InitialSegment cardinality (pos (suc n)) =
  suc n <=N cardinality
InitialSegment cardinality (negsuc n) =
  Bottom

EqualsInitialSegment : FiniteIntegerSet -> Set
EqualsInitialSegment finiteSet =
  (x : Int) ->
  Iff
    (member finiteSet x == true)
    (InitialSegment (size finiteSet) x)

FirstClaim : Set
FirstClaim =
  (finiteSet : FiniteIntegerSet) ->
  Qualifies finiteSet ->
  ContainsUnit finiteSet

SecondClaim : Set
SecondClaim =
  (finiteSet : FiniteIntegerSet) ->
  Qualifies finiteSet ->
  AllPositive finiteSet ->
  EqualsInitialSegment finiteSet

putnam-1982-b4 : Set
putnam-1982-b4 =
  Iff FirstClaim Top
  and
  Iff SecondClaim Top
