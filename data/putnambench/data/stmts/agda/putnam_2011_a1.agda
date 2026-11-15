-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_a1
-- (putnambench__agda__putnam_2011_a1): exactly 10053 integer points in the
-- 2011 by 2011 coordinate square cannot end a growing axis-aligned spiral.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_ _<=N_ _<N_ _<=Z_
infixr 3 _and_

data Bottom : Set where

record Top : Set where
  constructor truth

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data _<=Z_ : Int -> Int -> Set where
  negative<=positive :
    {m n : Nat} ->
    negsuc m <=Z pos n
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Predicate : Set -> Set1
Predicate A =
  A -> Set

record HasCardinality
  {A : Set}
  (member : Predicate A)
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
        (\ index -> item == enumerate index)

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

length : {A : Set} -> List A -> Nat
length [] =
  zero
length (_ ∷ xs) =
  suc (length xs)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

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

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

record Point : Set where
  constructor point
  field
    x-coordinate : Int
    y-coordinate : Int

open Point

origin : Point
origin =
  point (pos zero) (pos zero)

data Direction : Set where
  east north west south : Direction

nextDirection : Direction -> Direction
nextDirection east =
  north
nextDirection north =
  west
nextDirection west =
  south
nextDirection south =
  east

Step : Direction -> Nat -> Point -> Point -> Set
Step east segmentLength p q =
  (x-coordinate q == addInt (x-coordinate p) (pos segmentLength))
  and
  (y-coordinate q == y-coordinate p)
Step north segmentLength p q =
  (x-coordinate q == x-coordinate p)
  and
  (y-coordinate q == addInt (y-coordinate p) (pos segmentLength))
Step west segmentLength p q =
  (x-coordinate q == subtractInt (x-coordinate p) (pos segmentLength))
  and
  (y-coordinate q == y-coordinate p)
Step south segmentLength p q =
  (x-coordinate q == x-coordinate p)
  and
  (y-coordinate q == subtractInt (y-coordinate p) (pos segmentLength))

AllPositive : List Nat -> Set
AllPositive [] =
  Top
AllPositive (n ∷ ns) =
  (zero <N n) and AllPositive ns

StrictlyIncreasing : List Nat -> Set
StrictlyIncreasing [] =
  Top
StrictlyIncreasing (_ ∷ []) =
  Top
StrictlyIncreasing (m ∷ n ∷ ns) =
  (m <N n) and StrictlyIncreasing (n ∷ ns)

Follows :
  Direction ->
  List Nat ->
  List Point ->
  Set
Follows direction [] [] =
  Bottom
Follows direction [] (_ ∷ []) =
  Top
Follows direction [] (_ ∷ _ ∷ _) =
  Bottom
Follows direction (_ ∷ _) [] =
  Bottom
Follows direction (_ ∷ _) (_ ∷ []) =
  Bottom
Follows direction (segmentLength ∷ lengths) (p ∷ q ∷ points) =
  Step direction segmentLength p q
  and
  Follows (nextDirection direction) lengths (q ∷ points)

HeadIsOrigin : List Point -> Set
HeadIsOrigin [] =
  Bottom
HeadIsOrigin (p ∷ _) =
  p == origin

LastIs : List Point -> Point -> Set
LastIs [] endpoint =
  Bottom
LastIs (p ∷ []) endpoint =
  p == endpoint
LastIs (_ ∷ q ∷ points) endpoint =
  LastIs (q ∷ points) endpoint

GrowingSpiral : List Point -> Set
GrowingSpiral points =
  HeadIsOrigin points
  and
  Exists (List Nat)
    (\ lengths ->
      (suc (length lengths) == length points)
      and
      ((suc (suc zero) <=N length lengths)
      and
      (AllPositive lengths
      and
      (StrictlyIncreasing lengths
      and
      Follows east lengths points))))

InCoordinateSquare : Point -> Set
InCoordinateSquare p =
  ((pos zero <=Z x-coordinate p)
  and
  (x-coordinate p <=Z pos 2011))
  and
  ((pos zero <=Z y-coordinate p)
  and
  (y-coordinate p <=Z pos 2011))

CanEndGrowingSpiral : Point -> Set
CanEndGrowingSpiral endpoint =
  Exists (List Point)
    (\ points ->
      GrowingSpiral points
      and
      LastIs points endpoint)

UnreachablePoint : Point -> Set
UnreachablePoint p =
  InCoordinateSquare p
  and
  Not (CanEndGrowingSpiral p)

putnam-2011-a1 : Set
putnam-2011-a1 =
  HasCardinality UnreachablePoint 10053
