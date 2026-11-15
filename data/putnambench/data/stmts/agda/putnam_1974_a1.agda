-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_a1:
-- the maximum size of a conspiratorial subset of the integers from 1 through
-- 16 is 11. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

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

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

seven : Nat
seven =
  suc six

eight : Nat
eight =
  suc seven

nine : Nat
nine =
  suc eight

ten : Nat
ten =
  suc nine

eleven : Nat
eleven =
  suc ten

twelve : Nat
twelve =
  suc eleven

thirteen : Nat
thirteen =
  suc twelve

fourteen : Nat
fourteen =
  suc thirteen

fifteen : Nat
fifteen =
  suc fourteen

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

HasCommonFactor : Int -> Int -> Set
HasCommonFactor x y =
  two <=N naturalGCD (absInt x) (absInt y)

Subset : {A : Set} -> (A -> Set) -> (A -> Set) -> Set
Subset S T =
  (x : _) -> S x -> T x

InOneThroughSixteen : Int -> Set
InOneThroughSixteen x =
  Exists Nat
    (\ n ->
      n <=N fifteen
      and
      x == pos (suc n))

PairwiseDistinct : Int -> Int -> Int -> Set
PairwiseDistinct a b c =
  a != b
  and
  b != c
  and
  a != c

Conspiratorial : (Int -> Set) -> Set
Conspiratorial S =
  (a b c : Int) ->
  S a ->
  S b ->
  S c ->
  PairwiseDistinct a b c ->
  HasCommonFactor a b
  or
  HasCommonFactor b c
  or
  HasCommonFactor a c

record HasCardinality
  {A : Set}
  (S : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      S (enumerate index)
    enumeration-complete :
      (x : A) ->
      S x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record MaximumConspiratorialCardinality
  (maximum : Nat) :
  Set1 where

  field
    maximizing-set :
      Int -> Set
    maximizing-subset :
      Subset maximizing-set InOneThroughSixteen
    maximizing-conspiratorial :
      Conspiratorial maximizing-set
    maximizing-cardinality :
      HasCardinality maximizing-set maximum
    upper-bound :
      (S : Int -> Set) ->
      (cardinality : Nat) ->
      Subset S InOneThroughSixteen ->
      Conspiratorial S ->
      HasCardinality S cardinality ->
      cardinality <=N maximum

putnam-1974-a1 : Set1
putnam-1974-a1 =
  MaximumConspiratorialCardinality eleven
