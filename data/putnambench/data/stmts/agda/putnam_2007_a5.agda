-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_a5
-- (putnambench__agda__putnam_2007_a5): divisibility of one more than the
-- number of elements of prime order in a finite group. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

infix 4 _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor truth

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

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

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

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

record FiniteCarrier
  {a : Level}
  (A : Set a) :
  Set a where

  field
    cardinality :
      Nat
    has-cardinality :
      HasCardinality {A = A} (\ _ -> Top) cardinality

record Group
  {a : Level}
  (G : Set a) :
  Set a where

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
    multiply-associative :
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

open Group

one : Nat
one =
  suc zero

Divides :
  Nat ->
  Nat ->
  Set
Divides divisor number =
  Exists Nat
    (\ quotient ->
      number == divisor * quotient)

Prime :
  Nat ->
  Set
Prime p =
  one <N p
  and
  ((divisor : Nat) ->
    Divides divisor p ->
    divisor == one or divisor == p)

naturalPower :
  {a : Level} ->
  {G : Set a} ->
  Group G ->
  G ->
  Nat ->
  G
naturalPower group x zero =
  identity group
naturalPower group x (suc exponent) =
  multiply group
    (naturalPower group x exponent)
    x

HasOrder :
  {a : Level} ->
  {G : Set a} ->
  Group G ->
  G ->
  Nat ->
  Set a
HasOrder group x order =
  zero <N order
  and
  naturalPower group x order == identity group
  and
  ((exponent : Nat) ->
    zero <N exponent ->
    exponent <N order ->
    Not (naturalPower group x exponent == identity group))

putnam-2007-a5 :
  (a : Level) ->
  Set (lsuc a)
putnam-2007-a5 a =
  (G : Set a) ->
  (group : Group G) ->
  FiniteCarrier G ->
  (p n : Nat) ->
  Prime p ->
  HasCardinality
    (\ g -> HasOrder group g p)
    n ->
  n == zero or Divides p (n + one)
