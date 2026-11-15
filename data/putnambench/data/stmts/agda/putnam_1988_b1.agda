-- Statement-only formalization of PutnamBench corpus artifact putnam_1988_b1:
-- every product of two integers at least 2 is xy + xz + yz + 1 for some
-- positive integers x, y, and z. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

data Positive : Int -> Set where
  positive :
    {n : Nat} ->
    Positive (pos (suc n))

data AtLeastTwo : Int -> Set where
  at-least-two :
    {n : Nat} ->
    AtLeastTwo (pos (suc (suc n)))

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

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

oneZ : Int
oneZ =
  pos (suc zero)

putnam-1988-b1 : Set
putnam-1988-b1 =
  (a b : Int) ->
  AtLeastTwo a ->
  AtLeastTwo b ->
  Exists Int
    (\ x ->
      Exists Int
        (\ y ->
          Exists Int
            (\ z ->
              Positive x
              and
              Positive y
              and
              Positive z
              and
              multiplyInt a b
              ==
              addInt
                (addInt
                  (addInt
                    (multiplyInt x y)
                    (multiplyInt x z))
                  (multiplyInt y z))
                oneZ)))
