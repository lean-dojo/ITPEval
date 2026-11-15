-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_a1:
-- 578 is the least number of length-5 hops along integer-coordinate points
-- from (0,0) to (2021,2021). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2021A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixl 6 _+Z_ _-Z_
infixl 7 _*Z_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first-coordinate  : A
    second-coordinate : B

open Pair

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

negateZ : Int -> Int
negateZ (pos zero) =
  pos zero
negateZ (pos (suc n)) =
  negsuc n
negateZ (negsuc n) =
  pos (suc n)

_-Z_ : Int -> Int -> Int
x -Z y =
  x +Z negateZ y

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

length : {A : Set} -> List A -> Nat
length [] =
  zero
length (_ ∷ xs) =
  suc (length xs)

Point : Set
Point =
  Pair Int Int

origin : Point
origin =
  pos zero , pos zero

target : Point
target =
  pos 2021 , pos 2021

SquaredDistanceIs25 : Point -> Point -> Set
SquaredDistanceIs25 p q =
  ((first-coordinate p -Z first-coordinate q)
    *Z
   (first-coordinate p -Z first-coordinate q))
  +Z
  ((second-coordinate p -Z second-coordinate q)
    *Z
   (second-coordinate p -Z second-coordinate q))
  ==
  pos 25

data HopsFrom : Point -> List Point -> Set where
  no-hops :
    {start : Point} ->
    HopsFrom start []

  next-hop :
    {start next : Point} ->
    {remaining : List Point} ->
    SquaredDistanceIs25 start next ->
    HopsFrom next remaining ->
    HopsFrom start (next ∷ remaining)

data EndsAt : List Point -> Point -> Set where
  last-point :
    {point : Point} ->
    EndsAt (point ∷ []) point

  earlier-point :
    {point next endpoint : Point} ->
    {remaining : List Point} ->
    EndsAt (next ∷ remaining) endpoint ->
    EndsAt (point ∷ next ∷ remaining) endpoint

ValidHopCount : Nat -> Set
ValidHopCount k =
  Exists (List Point)
    (\ path ->
      HopsFrom origin path
      and
      EndsAt path target
      and
      length path == k)

record IsLeast (P : Nat -> Set) (least : Nat) : Set where
  field
    member      : P least
    lower-bound : (k : Nat) -> P k -> least <=N k

putnam-2021-a1 : Set
putnam-2021-a1 =
  IsLeast ValidHopCount 578
