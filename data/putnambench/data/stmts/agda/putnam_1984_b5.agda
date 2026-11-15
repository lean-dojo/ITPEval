-- Statement-only formalization of PutnamBench corpus artifact putnam_1984_b5:
-- the alternating sum of mth powers, signed by binary one-count parity, has
-- the closed form (-1)^m * 2^(m(m - 1)/2) * m!. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper; mod-helper)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

natLess : Nat -> Nat -> Bool
natLess zero zero =
  false
natLess zero (suc n) =
  true
natLess (suc m) zero =
  false
natLess (suc m) (suc n) =
  natLess m n

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  one
naturalPower base (suc exponent) =
  base * naturalPower base exponent

factorial : Nat -> Nat
factorial zero =
  one
factorial (suc n) =
  suc n * factorial n

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

integerPower : Int -> Nat -> Int
integerPower base zero =
  pos one
integerPower base (suc exponent) =
  multiplyInt base (integerPower base exponent)

sumFirstInt : Nat -> (Nat -> Int) -> Int
sumFirstInt zero term =
  pos zero
sumFirstInt (suc n) term =
  addInt
    (sumFirstInt n term)
    (term n)

binaryOneCountStep : (Nat -> Nat) -> Nat -> Nat
binaryOneCountStep d n with natLess n two
... | true =
  n
... | false =
  naturalMod n two + d (naturalDiv n two)

signedPowerSum : Nat -> (Nat -> Nat) -> Int
signedPowerSum m d =
  sumFirstInt (naturalPower two m)
    (\ k ->
      multiplyInt
        (integerPower (negsuc zero) (d k))
        (integerPower (pos k) m))

closedForm : Nat -> Int
closedForm m =
  multiplyInt
    (integerPower (negsuc zero) m)
    (multiplyInt
      (integerPower (pos two)
        (naturalDiv (m * (m - one)) two))
      (pos (factorial m)))

putnam-1984-b5 : Set
putnam-1984-b5 =
  (m : Nat) ->
  (d : Nat -> Nat) ->
  zero < m ->
  ((n : Nat) -> d n == binaryOneCountStep d n) ->
  signedPowerSum m d == closedForm m
