-- Statement-only formalization of Thousand Theorems corpus artifact Q26708,
-- "Binomial theorem": in every commutative semiring, the nth power of a sum
-- equals the binomial-coefficient-weighted finite sum. This file contains no proof.

{-# OPTIONS --safe #-}

module Q26708_binomial_theorem where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

record CommutativeSemiring
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x == x
    add-zero-right :
      (x : R) ->
      addR x zeroR == x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x == x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR == x

    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ==
      addR (multiplyR x z) (multiplyR y z)
    multiply-zero-left :
      (x : R) ->
      multiplyR zeroR x == zeroR
    multiply-zero-right :
      (x : R) ->
      multiplyR x zeroR == zeroR

oneN : Nat
oneN =
  suc zero

choose : Nat -> Nat -> Nat
choose n zero =
  oneN
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

natCast :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Nat ->
  R
natCast semiring zero =
  CommutativeSemiring.zeroR semiring
natCast semiring (suc n) =
  CommutativeSemiring.addR semiring
    (natCast semiring n)
    (CommutativeSemiring.oneR semiring)

power :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  R ->
  Nat ->
  R
power semiring x zero =
  CommutativeSemiring.oneR semiring
power semiring x (suc n) =
  CommutativeSemiring.multiplyR semiring
    (power semiring x n)
    x

sumThrough :
  {r : Level}
  {R : Set r} ->
  CommutativeSemiring R ->
  Nat ->
  (Nat -> R) ->
  R
sumThrough semiring zero terms =
  terms zero
sumThrough semiring (suc n) terms =
  CommutativeSemiring.addR semiring
    (sumThrough semiring n terms)
    (terms (suc n))

binomial-theorem : Setω
binomial-theorem =
  {r : Level} ->
  (R : Set r) ->
  (semiring : CommutativeSemiring R) ->
  (x y : R) ->
  (n : Nat) ->
  power semiring
    (CommutativeSemiring.addR semiring x y)
    n
  ==
  sumThrough semiring n
    (\ m ->
      CommutativeSemiring.multiplyR semiring
        (CommutativeSemiring.multiplyR semiring
          (power semiring x m)
          (power semiring y (n - m)))
        (natCast semiring (choose n m)))
