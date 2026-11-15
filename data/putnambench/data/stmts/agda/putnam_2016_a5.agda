-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_a5
-- (putnambench__agda__putnam_2016_a5): every element of the specified finite
-- two-generator group is a bounded product of signed g-h pairs. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2016A5 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_
infixr 3 _and_

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Empty : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Empty

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

Positive : Nat -> Set
Positive n =
  suc zero <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite
  {ell : Level}
  (A : Set ell) :
  Set ell where

  field
    size :
      Nat
    enumerate :
      Fin size ->
      A
    enumeration-complete :
      (x : A) ->
      Exists (Fin size)
        (\ i -> enumerate i == x)
    enumeration-injective :
      (i j : Fin size) ->
      enumerate i == enumerate j ->
      i == j

record Group
  {ell : Level}
  (G : Set ell) :
  Set ell where

  field
    identity :
      G
    multiply :
      G ->
      G ->
      G
    inverse :
      G ->
      G
    associative :
      (x y z : G) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    identity-left :
      (x : G) ->
      multiply identity x == x
    identity-right :
      (x : G) ->
      multiply x identity == x
    inverse-left :
      (x : G) ->
      multiply (inverse x) x == identity
    inverse-right :
      (x : G) ->
      multiply x (inverse x) == identity

open Finite
open Group

power :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Nat ->
  G
power structure x zero =
  identity structure
power structure x (suc n) =
  multiply structure x (power structure x n)

record IsElementOrder
  {ell : Level}
  {G : Set ell}
  (structure : Group G)
  (x : G)
  (n : Nat) :
  Set ell where

  field
    order-positive :
      Positive n
    power-is-identity :
      power structure x n == identity structure
    least-positive-power :
      (m : Nat) ->
      Positive m ->
      power structure x m == identity structure ->
      n <=N m

OddOrder :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Set ell
OddOrder structure x =
  Exists Nat
    (\ k ->
      IsElementOrder structure x (suc (k + k)))

data GeneratedByPair
  {ell : Level}
  {G : Set ell}
  (structure : Group G)
  (g h : G) :
  G ->
  Set ell where

  generated-g :
    GeneratedByPair structure g h g

  generated-h :
    GeneratedByPair structure g h h

  generated-identity :
    GeneratedByPair structure g h (identity structure)

  generated-product :
    {x y : G} ->
    GeneratedByPair structure g h x ->
    GeneratedByPair structure g h y ->
    GeneratedByPair structure g h (multiply structure x y)

  generated-inverse :
    {x : G} ->
    GeneratedByPair structure g h x ->
    GeneratedByPair structure g h (inverse structure x)

GeneratesPair :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  G ->
  Set ell
GeneratesPair {G = G} structure g h =
  (x : G) ->
  GeneratedByPair structure g h x

data GeneratedBySingle
  {ell : Level}
  {G : Set ell}
  (structure : Group G)
  (g : G) :
  G ->
  Set ell where

  generated-single :
    GeneratedBySingle structure g g

  generated-single-identity :
    GeneratedBySingle structure g (identity structure)

  generated-single-product :
    {x y : G} ->
    GeneratedBySingle structure g x ->
    GeneratedBySingle structure g y ->
    GeneratedBySingle structure g (multiply structure x y)

  generated-single-inverse :
    {x : G} ->
    GeneratedBySingle structure g x ->
    GeneratedBySingle structure g (inverse structure x)

GeneratesSingle :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Set ell
GeneratesSingle {G = G} structure g =
  (x : G) ->
  GeneratedBySingle structure g x

data Sign : Set where
  plus  : Sign
  minus : Sign

record SignedPair : Set where
  constructor signs
  field
    g-sign : Sign
    h-sign : Sign

open SignedPair

signedElement :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Sign ->
  G
signedElement structure x plus =
  x
signedElement structure x minus =
  inverse structure x

pairValue :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  G ->
  SignedPair ->
  G
pairValue structure g h pair =
  multiply structure
    (signedElement structure g (g-sign pair))
    (signedElement structure h (h-sign pair))

length :
  {ell : Level} ->
  {A : Set ell} ->
  List A ->
  Nat
length [] =
  zero
length (_ ∷ xs) =
  suc (length xs)

wordValue :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  G ->
  List SignedPair ->
  G
wordValue structure g h [] =
  identity structure
wordValue structure g h (pair ∷ pairs) =
  multiply structure
    (pairValue structure g h pair)
    (wordValue structure g h pairs)

putnam-2016-a5 :
  (ell : Level) ->
  Set (lsuc ell)
putnam-2016-a5 ell =
  (G : Set ell) ->
  (structure : Group G) ->
  (finite : Finite G) ->
  (g h : G) ->
  GeneratesPair structure g h ->
  Not (GeneratesSingle structure g) ->
  Not (GeneratesSingle structure h) ->
  OddOrder structure g ->
  (x : G) ->
  Exists (List SignedPair)
    (\ word ->
      Positive (length word)
      and
      (length word <=N size finite
      and
      wordValue structure g h word == x))
