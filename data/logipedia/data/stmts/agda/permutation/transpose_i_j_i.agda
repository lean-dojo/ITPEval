-- Statement-only formalization of Logipedia corpus artifact
-- permutation.transpose_i_j_i (catalog title "permutation.transpose_i_j_i"):
-- transposing two natural numbers sends the first selected number to the
-- second. This file contains no proof.

{-# OPTIONS --safe #-}

module transpose_i_j_i where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)

equalNat : Nat -> Nat -> Bool
equalNat zero zero = true
equalNat zero (suc n) = false
equalNat (suc m) zero = false
equalNat (suc m) (suc n) = equalNat m n

ifThenElse : {A : Set} -> Bool -> A -> A -> A
ifThenElse true whenTrue whenFalse = whenTrue
ifThenElse false whenTrue whenFalse = whenFalse

transpose : Nat -> Nat -> Nat -> Nat
transpose i j n =
  ifThenElse
    (equalNat n i)
    j
    (ifThenElse (equalNat n j) i n)

transpose-i-j-i : Set
transpose-i-j-i =
  (i j : Nat) ->
  transpose i j i ≡ j
