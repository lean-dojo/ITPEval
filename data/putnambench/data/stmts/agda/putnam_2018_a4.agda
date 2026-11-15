-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_a4
-- (putnambench__agda__putnam_2018_a4): floor-difference exponents from
-- positive coprime integers force two group elements to commute when their
-- ordered alternating product is the identity. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper; mod-helper)
open import Agda.Primitive using (Level; lsuc)

infix 4 _<=N_

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

one : Nat
one =
  suc zero

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

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b =
  a
gcdWithFuel (suc fuel) a zero =
  a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat -> Nat -> Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

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
  multiply structure
    (power structure x exponent)
    x

floorDifferenceSequence :
  Nat ->
  Nat ->
  (Nat -> Nat) ->
  Set
floorDifferenceSequence m n a =
  (k : Nat) ->
  Positive k ->
  k <=N n ->
  a k ==
  naturalDiv (m * k) n -
  naturalDiv (m * (k - one)) n

orderedProduct :
  {ell : Level} ->
  {G : Set ell} ->
  Group G ->
  G ->
  G ->
  (Nat -> Nat) ->
  Nat ->
  G
orderedProduct structure g h a zero =
  identity structure
orderedProduct structure g h a (suc k) =
  multiply structure
    (multiply structure
      (orderedProduct structure g h a k)
      g)
    (power structure h (a (suc k)))

putnam-2018-a4 :
  (ell : Level) ->
  Set (lsuc ell)
putnam-2018-a4 ell =
  (m n : Nat) ->
  Positive m ->
  Positive n ->
  naturalGCD m n == one ->
  (a : Nat -> Nat) ->
  floorDifferenceSequence m n a ->
  (G : Set ell) ->
  (structure : Group G) ->
  (g h : G) ->
  orderedProduct structure g h a n == identity structure ->
  multiply structure g h == multiply structure h g
