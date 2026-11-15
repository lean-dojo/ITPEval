-- Statement-only formalization of thousand-theorems corpus artifact Q718875,
-- "Erdős–Ko–Rado theorem": an intersecting family of r-subsets of Fin n,
-- with r at most floor (n / 2), has at most choose (n - 1) (r - 1)
-- members. This file contains no proof.

{-# OPTIONS --safe #-}

module Q718875_erd_s_ko_rado_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 5 _L::_
infixr 6 _&&_
infixr 5 _||_
infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data Vec (A : Set) : Nat -> Set where
  VNil  : Vec A zero
  _V::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

data List (A : Set) : Set where
  LNil  : List A
  _L::_ : A -> List A -> List A

Subset : Nat -> Set
Subset n =
  Vec Bool n

Family : Nat -> Set
Family n =
  Subset n -> Bool

data IsTrue : Bool -> Set where
  true-witness : IsTrue true

_&&_ : Bool -> Bool -> Bool
true && right =
  right
false && right =
  false

_||_ : Bool -> Bool -> Bool
true || right =
  true
false || right =
  right

map-list :
  {A B : Set} ->
  (A -> B) ->
  List A ->
  List B
map-list function LNil =
  LNil
map-list function (item L:: items) =
  function item L:: map-list function items

append :
  {A : Set} ->
  List A ->
  List A ->
  List A
append LNil right =
  right
append (item L:: items) right =
  item L:: append items right

all-subsets : (n : Nat) -> List (Subset n)
all-subsets zero =
  VNil L:: LNil
all-subsets (suc n) =
  append
    (map-list (\ tail -> false V:: tail) (all-subsets n))
    (map-list (\ tail -> true V:: tail) (all-subsets n))

count-where :
  {A : Set} ->
  (A -> Bool) ->
  List A ->
  Nat
count-where predicate LNil =
  zero
count-where predicate (item L:: items) with predicate item
... | false =
  count-where predicate items
... | true =
  suc (count-where predicate items)

subset-cardinality :
  {n : Nat} ->
  Subset n ->
  Nat
subset-cardinality VNil =
  zero
subset-cardinality (false V:: tail) =
  subset-cardinality tail
subset-cardinality (true V:: tail) =
  suc (subset-cardinality tail)

subsets-intersect :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Bool
subsets-intersect VNil VNil =
  false
subsets-intersect
  (left V:: left-tail)
  (right V:: right-tail) =
  (left && right) || subsets-intersect left-tail right-tail

family-size :
  (n : Nat) ->
  Family n ->
  Nat
family-size n family =
  count-where family (all-subsets n)

Sized :
  {n : Nat} ->
  Family n ->
  Nat ->
  Set
Sized {n} family r =
  (subset : Subset n) ->
  IsTrue (family subset) ->
  subset-cardinality subset == r

Intersecting :
  {n : Nat} ->
  Family n ->
  Set
Intersecting {n} family =
  (left right : Subset n) ->
  IsTrue (family left) ->
  IsTrue (family right) ->
  IsTrue (subsets-intersect left right)

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

one : Nat
one =
  suc zero

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

erdos-ko-rado-theorem : Set
erdos-ko-rado-theorem =
  (n r : Nat) ->
  (family : Family n) ->
  Intersecting family ->
  Sized family r ->
  r <= half n ->
  family-size n family <= choose (pred n) (pred r)
