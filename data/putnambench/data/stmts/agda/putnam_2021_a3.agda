-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_a3:
-- positive integers whose corresponding sphere contains an integer-coordinate
-- regular tetrahedron are exactly the numbers 3 times a positive square.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2021A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

absoluteDifference : Nat -> Nat -> Nat
absoluteDifference zero n =
  n
absoluteDifference m zero =
  m
absoluteDifference (suc m) (suc n) =
  absoluteDifference m n

absoluteIntegerDifference : Int -> Int -> Nat
absoluteIntegerDifference (pos m) (pos n) =
  absoluteDifference m n
absoluteIntegerDifference (pos m) (negsuc n) =
  suc (m + n)
absoluteIntegerDifference (negsuc m) (pos n) =
  suc (m + n)
absoluteIntegerDifference (negsuc m) (negsuc n) =
  absoluteDifference m n

integerSquare : Int -> Nat
integerSquare (pos magnitude) =
  magnitude * magnitude
integerSquare (negsuc predecessor) =
  suc predecessor * suc predecessor

record Point3 : Set where
  constructor point3
  field
    x-coordinate : Int
    y-coordinate : Int
    z-coordinate : Int

open Point3

squaredNorm : Point3 -> Nat
squaredNorm p =
  integerSquare (x-coordinate p) +
  (integerSquare (y-coordinate p) +
   integerSquare (z-coordinate p))

squaredDistance : Point3 -> Point3 -> Nat
squaredDistance p q =
  let
    x-difference =
      absoluteIntegerDifference
        (x-coordinate p)
        (x-coordinate q)
    y-difference =
      absoluteIntegerDifference
        (y-coordinate p)
        (y-coordinate q)
    z-difference =
      absoluteIntegerDifference
        (z-coordinate p)
        (z-coordinate q)
  in
  x-difference * x-difference +
  (y-difference * y-difference +
   z-difference * z-difference)

OnSphere : Nat -> Point3 -> Set
OnSphere N p =
  squaredNorm p == N

RegularTetrahedron : Point3 -> Point3 -> Point3 -> Point3 -> Set
RegularTetrahedron A B C D =
  Exists Nat
    (\ common-squared-edge ->
      zero <N common-squared-edge
      and
      squaredDistance A B == common-squared-edge
      and
      squaredDistance A C == common-squared-edge
      and
      squaredDistance A D == common-squared-edge
      and
      squaredDistance B C == common-squared-edge
      and
      squaredDistance B D == common-squared-edge
      and
      squaredDistance C D == common-squared-edge)

HasInscribedIntegerRegularTetrahedron : Nat -> Set
HasInscribedIntegerRegularTetrahedron N =
  Exists Point3
    (\ A ->
      Exists Point3
        (\ B ->
          Exists Point3
            (\ C ->
              Exists Point3
                (\ D ->
                  OnSphere N A
                  and
                  OnSphere N B
                  and
                  OnSphere N C
                  and
                  OnSphere N D
                  and
                  RegularTetrahedron A B C D))))

three : Nat
three =
  suc (suc (suc zero))

Solution : Nat -> Set
Solution N =
  Exists Nat
    (\ m ->
      zero <N m
      and
      N == three * (m * m))

putnam-2021-a3 : Set
putnam-2021-a3 =
  (N : Nat) ->
  Iff
    (zero <N N and HasInscribedIntegerRegularTetrahedron N)
    (Solution N)
