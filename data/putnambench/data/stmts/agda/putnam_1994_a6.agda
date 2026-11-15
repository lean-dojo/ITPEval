-- Statement-only formalization of PutnamBench corpus artifact putnam_1994_a6
-- (putnambench__agda__putnam_1994_a6): among the distinct functions formed
-- by binary ordered compositions of ten integer permutations generating every
-- integer from zero, at most 512 stabilize any nonempty finite integer set.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=N_
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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Fin10 : Set where
  i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 : Fin10

data NonemptyList {A : Set} : List A -> Set where
  nonempty : (x : A) -> (xs : List A) -> NonemptyList (x ∷ xs)

record Permutation (A : Set) : Set where
  field
    apply         : A -> A
    inverse       : A -> A
    inverse-apply : (x : A) -> inverse (apply x) == x
    apply-inverse : (x : A) -> apply (inverse x) == x

open Permutation

FunctionEqual :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
FunctionEqual left right =
  (x : _) ->
  left x == right x

SetEqual :
  {A : Set} ->
  (A -> Set) ->
  (A -> Set) ->
  Set
SetEqual left right =
  (x : _) ->
  Iff (left x) (right x)

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

FiniteSet :
  {A : Set} ->
  (A -> Set) ->
  Set
FiniteSet member =
  Exists Nat
    (\ cardinality ->
      HasExtensionalCardinality _==_ member cardinality)

NonemptySet :
  {A : Set} ->
  (A -> Set) ->
  Set
NonemptySet member =
  Exists _
    (\ item -> member item)

CardinalityAtMost :
  {A : Set} ->
  (A -> A -> Set) ->
  (A -> Set) ->
  Nat ->
  Set
CardinalityAtMost equivalent member bound =
  Exists Nat
    (\ cardinality ->
      HasExtensionalCardinality equivalent member cardinality
      and
      cardinality <=N bound)

composeWord :
  (Fin10 -> Permutation Int) ->
  List Fin10 ->
  Int ->
  Int
composeWord f [] x =
  x
composeWord f (index ∷ rest) x =
  apply (f index) (composeWord f rest x)

GeneratesIntegersFromZero :
  (Fin10 -> Permutation Int) ->
  Set
GeneratesIntegersFromZero f =
  (n : Int) ->
  Exists (List Fin10)
    (\ indices ->
      NonemptyList indices
      and
      composeWord f indices (pos zero) == n)

selectPower :
  Bool ->
  Permutation Int ->
  Int ->
  Int
selectPower false permutation x =
  x
selectPower true permutation x =
  apply permutation x

binaryComposition :
  (Fin10 -> Permutation Int) ->
  (Fin10 -> Bool) ->
  Int ->
  Int
binaryComposition f exponent x =
  selectPower (exponent i0) (f i0)
    (selectPower (exponent i1) (f i1)
      (selectPower (exponent i2) (f i2)
        (selectPower (exponent i3) (f i3)
          (selectPower (exponent i4) (f i4)
            (selectPower (exponent i5) (f i5)
              (selectPower (exponent i6) (f i6)
                (selectPower (exponent i7) (f i7)
                  (selectPower (exponent i8) (f i8)
                    (selectPower (exponent i9) (f i9) x)))))))))

InBinaryFamily :
  (Fin10 -> Permutation Int) ->
  (Int -> Int) ->
  Set
InBinaryFamily f g =
  Exists (Fin10 -> Bool)
    (\ exponent ->
      FunctionEqual g (binaryComposition f exponent))

Image :
  (Int -> Int) ->
  (Int -> Set) ->
  Int ->
  Set
Image g member y =
  Exists Int
    (\ x ->
      member x
      and
      g x == y)

Stabilizes :
  (Int -> Int) ->
  (Int -> Set) ->
  Set
Stabilizes g member =
  SetEqual (Image g member) member

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fiveHundredTwelveN : Nat
fiveHundredTwelveN =
  twoN * twoN * twoN * twoN * twoN * twoN * twoN * twoN * twoN

putnam-1994-a6 : Set1
putnam-1994-a6 =
  (f : Fin10 -> Permutation Int) ->
  GeneratesIntegersFromZero f ->
  (A : Int -> Set) ->
  FiniteSet A ->
  NonemptySet A ->
  CardinalityAtMost
    FunctionEqual
    (\ g ->
      InBinaryFamily f g
      and
      Stabilizes g A)
    fiveHundredTwelveN
