-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_b6
-- (putnambench__agda__putnam_2005_b6): the signed sum over permutations,
-- weighted by one plus the number of fixed points, has the stated rational
-- value. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005B6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; _*_; suc; zero)

infix 4 _<=N_ _~Q_
infixr 5 _::_

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

one : Nat
one =
  suc zero

Positive : Nat -> Set
Positive n =
  one <=N n

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

weakenFin : {n : Nat} -> Fin n -> Fin (suc n)
weakenFin fzero =
  fzero
weakenFin (fsuc index) =
  fsuc (weakenFin index)

lastFin : (n : Nat) -> Fin (suc n)
lastFin zero =
  fzero
lastFin (suc n) =
  fsuc (lastFin n)

mapVec :
  {A B : Set} ->
  {n : Nat} ->
  (A -> B) ->
  Vec A n ->
  Vec B n
mapVec f [] =
  []
mapVec f (x :: xs) =
  f x :: mapVec f xs

insertAt :
  {A : Set} ->
  {n : Nat} ->
  Fin (suc n) ->
  A ->
  Vec A n ->
  Vec A (suc n)
insertAt fzero x xs =
  x :: xs
insertAt (fsuc position) x (y :: ys) =
  y :: insertAt position x ys

data PermutationCode : Nat -> Set where
  empty  : PermutationCode zero
  insert :
    {n : Nat} ->
    Fin (suc n) ->
    PermutationCode n ->
    PermutationCode (suc n)

oneLine :
  {n : Nat} ->
  PermutationCode n ->
  Vec (Fin n) n
oneLine empty =
  []
oneLine (insert {n} position permutation) =
  insertAt
    position
    (lastFin n)
    (mapVec weakenFin (oneLine permutation))

sameFin :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Bool
sameFin fzero fzero =
  true
sameFin fzero (fsuc right) =
  false
sameFin (fsuc left) fzero =
  false
sameFin (fsuc left) (fsuc right) =
  sameFin left right

incrementIf : Bool -> Nat -> Nat
incrementIf true n =
  suc n
incrementIf false n =
  n

countMatching :
  {length total : Nat} ->
  (Fin length -> Fin total) ->
  Vec (Fin total) length ->
  Nat
countMatching {zero} position [] =
  zero
countMatching {suc length} position (x :: xs) =
  incrementIf
    (sameFin x (position fzero))
    (countMatching
      (\ index -> position (fsuc index))
      xs)

fixedPointCount :
  {n : Nat} ->
  PermutationCode n ->
  Nat
fixedPointCount permutation =
  countMatching
    (\ index -> index)
    (oneLine permutation)

evenNat : Nat -> Bool
evenNat zero =
  true
evenNat (suc zero) =
  false
evenNat (suc (suc n)) =
  evenNat n

data Sign : Set where
  positive : Sign
  negative : Sign

flipSign : Sign -> Sign
flipSign positive =
  negative
flipSign negative =
  positive

multiplySign : Sign -> Sign -> Sign
multiplySign positive sign =
  sign
multiplySign negative sign =
  flipSign sign

signFromParity : Nat -> Sign
signFromParity n with evenNat n
... | true =
  positive
... | false =
  negative

permutationSign :
  {n : Nat} ->
  PermutationCode n ->
  Sign
permutationSign empty =
  positive
permutationSign (insert {n} position permutation) =
  multiplySign
    (signFromParity (n - toNat position))
    (permutationSign permutation)

negativeInt : Nat -> Int
negativeInt zero =
  pos zero
negativeInt (suc n) =
  negsuc n

signedNat : Sign -> Nat -> Int
signedNat positive n =
  pos n
signedNat negative n =
  negativeInt n

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
  negativeInt (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeInt (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

scaleInt : Int -> Nat -> Int
scaleInt integer natural =
  multiplyInt integer (pos natural)

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator rational =
  suc (denominator-minus-one rational)

_~Q_ : Rational -> Rational -> Set
left ~Q right =
  scaleInt (numerator left) (denominator right)
  ==
  scaleInt (numerator right) (denominator left)

zeroQ : Rational
zeroQ =
  fraction (pos zero) zero

addQ : Rational -> Rational -> Rational
addQ left right =
  fraction
    (addInt
      (scaleInt (numerator left) (denominator right))
      (scaleInt (numerator right) (denominator left)))
    (predecessor (denominator left * denominator right))

sumFin :
  {n : Nat} ->
  (Fin n -> Rational) ->
  Rational
sumFin {zero} term =
  zeroQ
sumFin {suc n} term =
  addQ
    (term fzero)
    (sumFin (\ index -> term (fsuc index)))

sumPermutations :
  (n : Nat) ->
  (PermutationCode n -> Rational) ->
  Rational
sumPermutations zero term =
  term empty
sumPermutations (suc n) term =
  sumFin
    (\ position ->
      sumPermutations n
        (\ permutation ->
          term (insert position permutation)))

permutationTerm :
  {n : Nat} ->
  PermutationCode n ->
  Rational
permutationTerm permutation =
  fraction
    (signedNat (permutationSign permutation) one)
    (fixedPointCount permutation)

rightSide : Nat -> Rational
rightSide n =
  fraction
    (signedNat (signFromParity (suc n)) n)
    n

putnam-2005-b6 : Set
putnam-2005-b6 =
  (n : Nat) ->
  Positive n ->
  sumPermutations n permutationTerm
  ~Q
  rightSide n
