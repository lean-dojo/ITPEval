-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_a5
-- (putnambench__agda__putnam_2025_a5): the sign sequences maximizing the
-- number of permutations with prescribed adjacent ascent and descent signs
-- are exactly the two alternating sequences. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025A5 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_
infixr 5 _::_
infixr 3 _andB_
infixr 2 _or_

data _or_ (A B : Set) : Set where
  left-injection  : A -> A or B
  right-injection : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

data List (A : Set) : Set where
  []L   : List A
  _::L_ : A -> List A -> List A

mapList :
  {A B : Set} ->
  (A -> B) ->
  List A ->
  List B
mapList function []L =
  []L
mapList function (x ::L xs) =
  function x ::L mapList function xs

appendList :
  {A : Set} ->
  List A ->
  List A ->
  List A
appendList []L ys =
  ys
appendList (x ::L xs) ys =
  x ::L appendList xs ys

concatMap :
  {A B : Set} ->
  (A -> List B) ->
  List A ->
  List B
concatMap function []L =
  []L
concatMap function (x ::L xs) =
  appendList (function x) (concatMap function xs)

allFin : (n : Nat) -> List (Fin n)
allFin zero =
  []L
allFin (suc n) =
  fzero ::L mapList fsuc (allFin n)

allVectors :
  {A : Set} ->
  (length : Nat) ->
  List A ->
  List (Vec A length)
allVectors zero alphabet =
  [] ::L []L
allVectors (suc length) alphabet =
  concatMap
    (\ x ->
      mapList
        (\ tail -> x :: tail)
        (allVectors length alphabet))
    alphabet

notB : Bool -> Bool
notB true =
  false
notB false =
  true

_andB_ : Bool -> Bool -> Bool
true andB right =
  right
false andB right =
  false

finEqual : {n : Nat} -> Fin n -> Fin n -> Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc right) =
  false
finEqual (fsuc left) fzero =
  false
finEqual (fsuc left) (fsuc right) =
  finEqual left right

memberFin :
  {bound length : Nat} ->
  Fin bound ->
  Vec (Fin bound) length ->
  Bool
memberFin value [] =
  false
memberFin value (x :: xs) with finEqual value x
... | true =
  true
... | false =
  memberFin value xs

allDistinct :
  {bound length : Nat} ->
  Vec (Fin bound) length ->
  Bool
allDistinct [] =
  true
allDistinct (x :: xs) =
  notB (memberFin x xs) andB allDistinct xs

lessNat : Nat -> Nat -> Bool
lessNat zero zero =
  false
lessNat zero (suc right) =
  true
lessNat (suc left) zero =
  false
lessNat (suc left) (suc right) =
  lessNat left right

data Sign : Set where
  plus  : Sign
  minus : Sign

signedIncrease :
  {n : Nat} ->
  Sign ->
  Fin n ->
  Fin n ->
  Bool
signedIncrease plus left-value right-value =
  lessNat (toNat left-value) (toNat right-value)
signedIncrease minus left-value right-value =
  lessNat (toNat right-value) (toNat left-value)

hasRequiredSigns :
  {n bound : Nat} ->
  (Fin n -> Sign) ->
  Vec (Fin bound) (suc n) ->
  Bool
hasRequiredSigns {zero} signs (x :: []) =
  true
hasRequiredSigns {suc n} signs (x :: y :: rest) =
  signedIncrease (signs fzero) x y
  andB
  hasRequiredSigns
    (\ index -> signs (fsuc index))
    (y :: rest)

isQualifyingPermutation :
  {n : Nat} ->
  (Fin n -> Sign) ->
  Vec (Fin (suc n)) (suc n) ->
  Bool
isQualifyingPermutation signs values =
  allDistinct values andB hasRequiredSigns signs values

countSatisfying :
  {A : Set} ->
  (A -> Bool) ->
  List A ->
  Nat
countSatisfying predicate []L =
  zero
countSatisfying predicate (x ::L xs) with predicate x
... | true =
  suc (countSatisfying predicate xs)
... | false =
  countSatisfying predicate xs

f : (n : Nat) -> (Fin n -> Sign) -> Nat
f n signs =
  countSatisfying
    (isQualifyingPermutation signs)
    (allVectors (suc n) (allFin (suc n)))

flipSign : Sign -> Sign
flipSign plus =
  minus
flipSign minus =
  plus

alternatingFrom :
  {n : Nat} ->
  Sign ->
  Fin n ->
  Sign
alternatingFrom start fzero =
  start
alternatingFrom start (fsuc index) =
  alternatingFrom (flipSign start) index

PointwiseEqual :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
PointwiseEqual {A} left-function right-function =
  (x : A) ->
  left-function x == right-function x

AlternatingSolution :
  {n : Nat} ->
  (Fin n -> Sign) ->
  Set
AlternatingSolution signs =
  PointwiseEqual signs (alternatingFrom minus)
  or
  PointwiseEqual signs (alternatingFrom plus)

putnam-2025-a5 : Set
putnam-2025-a5 =
  (n : Nat) ->
  Positive n ->
  (signs : Fin n -> Sign) ->
  Iff
    ((other-signs : Fin n -> Sign) ->
      f n other-signs <=N f n signs)
    (AlternatingSolution signs)
