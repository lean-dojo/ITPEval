-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_a1
-- (putnambench__agda__putnam_2019_a1): the values of
-- A^3 + B^3 + C^3 - 3ABC for nonnegative integers are exactly the
-- nonnegative integers not congruent to 3 or 6 modulo 9. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+Z_
infixl 7 _*Z_
infixr 3 _and_
infix 1 _iff_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

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

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

sixN : Nat
sixN =
  threeN + threeN

nineN : Nat
nineN =
  threeN * threeN

threeZ : Int
threeZ =
  pos threeN

sixZ : Int
sixZ =
  pos sixN

nineZ : Int
nineZ =
  pos nineN

cube : Int -> Int
cube x =
  (x *Z x) *Z x

data Nonnegative : Int -> Set where
  nonnegative :
    {n : Nat} ->
    Nonnegative (pos n)

CongruentModuloNine : Int -> Int -> Set
CongruentModuloNine value residue =
  Exists Int
    (\ quotient ->
      value == residue +Z (nineZ *Z quotient))

RepresentableValue : Int -> Set
RepresentableValue n =
  Exists Int
    (\ A ->
      Exists Int
        (\ B ->
          Exists Int
            (\ C ->
              Nonnegative A
              and
              Nonnegative B
              and
              Nonnegative C
              and
              (cube A +Z cube B +Z cube C
                +Z negateInt (threeZ *Z A *Z B *Z C))
                == n)))

putnam-2019-a1-solution : Int -> Set
putnam-2019-a1-solution n =
  Nonnegative n
  and
  Not (CongruentModuloNine n threeZ)
  and
  Not (CongruentModuloNine n sixZ)

putnam-2019-a1 : Set
putnam-2019-a1 =
  (n : Int) ->
  RepresentableValue n iff putnam-2019-a1-solution n
