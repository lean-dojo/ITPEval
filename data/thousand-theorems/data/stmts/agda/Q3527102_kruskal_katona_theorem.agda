-- Statement-only formalization of thousand-theorems corpus artifact Q3527102
-- (thousand-theorems__agda__Q3527102), "Kruskal–Katona theorem": if A is a
-- family of r-subsets of Fin n and C is a colex initial segment of r-subsets
-- with no more members than A, then C's shadow has no more members than A's
-- shadow. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527102_kruskal_katona_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 5 _L::_
infixr 6 _&&_
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

bool-implies : Bool -> Bool -> Bool
bool-implies false right =
  true
bool-implies true right =
  right

bool-lt : Bool -> Bool -> Bool
bool-lt false false =
  false
bool-lt false true =
  true
bool-lt true right =
  false

nat-equal : Nat -> Nat -> Bool
nat-equal zero zero =
  true
nat-equal zero (suc right) =
  false
nat-equal (suc left) zero =
  false
nat-equal (suc left) (suc right) =
  nat-equal left right

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

any-list :
  {A : Set} ->
  (A -> Bool) ->
  List A ->
  Bool
any-list predicate LNil =
  false
any-list predicate (item L:: items) with predicate item
... | true =
  true
... | false =
  any-list predicate items

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

same-subset :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Bool
same-subset VNil VNil =
  true
same-subset (false V:: left) (false V:: right) =
  same-subset left right
same-subset (false V:: left) (true V:: right) =
  false
same-subset (true V:: left) (false V:: right) =
  false
same-subset (true V:: left) (true V:: right) =
  same-subset left right

subset-of :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Bool
subset-of VNil VNil =
  true
subset-of (left V:: left-tail) (right V:: right-tail) =
  bool-implies left right && subset-of left-tail right-tail

colex-lt :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Bool
colex-lt VNil VNil =
  false
colex-lt
  (left V:: left-tail)
  (right V:: right-tail)
  with same-subset left-tail right-tail
... | true =
  bool-lt left right
... | false =
  colex-lt left-tail right-tail

remove-one :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Bool
remove-one smaller larger =
  subset-of smaller larger &&
  nat-equal
    (suc (subset-cardinality smaller))
    (subset-cardinality larger)

family-size :
  (n : Nat) ->
  Family n ->
  Nat
family-size n family =
  count-where family (all-subsets n)

shadow-member :
  (n : Nat) ->
  Family n ->
  Subset n ->
  Bool
shadow-member n family smaller =
  any-list
    (\ larger -> family larger && remove-one smaller larger)
    (all-subsets n)

shadow-size :
  (n : Nat) ->
  Family n ->
  Nat
shadow-size n family =
  count-where (shadow-member n family) (all-subsets n)

Sized :
  {n : Nat} ->
  Family n ->
  Nat ->
  Set
Sized {n} family r =
  (subset : Subset n) ->
  IsTrue (family subset) ->
  subset-cardinality subset == r

record IsInitialColexSegment
  {n : Nat}
  (family : Family n)
  (r : Nat) :
  Set where

  field
    sized :
      Sized family r

    downward-closed :
      (larger smaller : Subset n) ->
      IsTrue (family larger) ->
      IsTrue (colex-lt smaller larger) ->
      subset-cardinality smaller == r ->
      IsTrue (family smaller)

kruskal-katona-theorem :
  Set
kruskal-katona-theorem =
  (n r : Nat) ->
  (A C : Family n) ->
  Sized A r ->
  family-size n C <= family-size n A ->
  IsInitialColexSegment C r ->
  shadow-size n C <= shadow-size n A
