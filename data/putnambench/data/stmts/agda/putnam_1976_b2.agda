-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_b2:
-- a two-generator group with the stated relations has exactly eight square
-- elements, represented by the specified words in the generators. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam1976B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {a p : Level}
  {A : Set a}
  (P : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ p) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record Group
  {ell : Level}
  (G : Set ell) :
  Set ell where

  field
    identity       : G
    inverse        : G -> G
    multiply       : G -> G -> G
    associative    : (x y z : G) ->
                     multiply (multiply x y) z ==
                     multiply x (multiply y z)
    identity-left  : (x : G) -> multiply identity x == x
    identity-right : (x : G) -> multiply x identity == x
    inverse-left   : (x : G) -> multiply (inverse x) x == identity
    inverse-right  : (x : G) -> multiply x (inverse x) == identity

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
power structure x (suc exponent) =
  multiply structure (power structure x exponent) x

integerPower :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Int ->
  G
integerPower structure x (pos exponent) =
  power structure x exponent
integerPower structure x (negsuc exponent) =
  power structure (inverse structure x) (suc exponent)

record IntPair : Set where
  constructor _,_
  field
    first  : Int
    second : Int

word :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  G ->
  List IntPair ->
  G
word structure A B [] =
  identity structure
word structure A B ((m , n) ∷ rest) =
  multiply structure
    (multiply structure
      (integerPower structure A m)
      (integerPower structure B n))
    (word structure A B rest)

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

singletonWord :
  Nat ->
  Nat ->
  List IntPair
singletonWord m n =
  (pos m , pos n) ∷ []

SolutionWord :
  List IntPair ->
  Set
SolutionWord w =
  w == singletonWord zero zero
  or
  w == singletonWord two zero
  or
  w == singletonWord zero one
  or
  w == singletonWord zero two
  or
  w == singletonWord zero three
  or
  w == singletonWord zero four
  or
  w == singletonWord zero five
  or
  w == singletonWord zero six

Square :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  Set ell
Square {G = G} structure g =
  Exists G
    (\ C ->
      multiply structure C C == g)

RepresentedSquare :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  G ->
  G ->
  Set ell
RepresentedSquare structure A B g =
  Exists (List IntPair)
    (\ w ->
      SolutionWord w
      and
      g == word structure A B w)

putnam-1976-b2 :
  (ell : Level) ->
  Set (lsuc ell)
putnam-1976-b2 ell =
  (G : Set ell) ->
  (structure : Group G) ->
  (A B : G) ->
  (power structure A four == identity structure
    and
    power structure A two != identity structure) ->
  (power structure B seven == identity structure
    and
    B != identity structure) ->
  multiply structure
    (multiply structure
      (multiply structure A B)
      (inverse structure A))
    B
  ==
  identity structure ->
  ((g : G) ->
    Exists (List IntPair)
      (\ w -> g == word structure A B w)) ->
  (S : G -> Set ell) ->
  ((g : G) -> Iff (S g) (Square structure g)) ->
  HasCardinality S eight
  and
  ((g : G) ->
    Iff
      (S g)
      (RepresentedSquare structure A B g))
