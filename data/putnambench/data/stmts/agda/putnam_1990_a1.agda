-- Statement-only formalization of PutnamBench corpus artifact putnam_1990_a1:
-- the integer sequence with the specified third-order recurrence equals
-- n factorial plus 2 to the nth power. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

factorial : Nat -> Nat
factorial zero =
  1
factorial (suc n) =
  suc n * factorial n

twoPower : Nat -> Nat
twoPower zero =
  1
twoPower (suc n) =
  2 * twoPower n

closedForm : Nat -> Int
closedForm n =
  addInt
    (pos (factorial n))
    (pos (twoPower n))

record InitialValues (T : Nat -> Int) : Set where
  field
    value-zero : T 0 == pos 2
    value-one  : T 1 == pos 3
    value-two  : T 2 == pos 6

recurrenceRightHandSide :
  (Nat -> Int) ->
  Nat ->
  Int
recurrenceRightHandSide T n =
  addInt
    (subtractInt
      (multiplyInt
        (pos (n + 7))
        (T (n + 2)))
      (multiplyInt
        (multiplyInt
          (pos 4)
          (pos (n + 3)))
        (T (n + 1))))
    (multiplyInt
      (pos (4 * n + 4))
      (T n))

Recurrence : (Nat -> Int) -> Set
Recurrence T =
  (n : Nat) ->
  T (n + 3) == recurrenceRightHandSide T n

putnam-1990-a1 : Set
putnam-1990-a1 =
  (T : Nat -> Int) ->
  InitialValues T ->
  Recurrence T ->
  (n : Nat) ->
  T n == closedForm n
