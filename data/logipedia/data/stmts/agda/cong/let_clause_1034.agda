-- Statement-only formalization of Logipedia corpus artifact
-- cong.let_clause_1034 (catalog title "cong.let_clause_1034"): the total
-- natural quotient and remainder operations satisfy the quotient-remainder
-- decomposition under the source theorem's positive-modulus context. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-1034 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero m n = m
mod-aux (suc fuel) m n with leb m n
... | true = m
... | false = mod-aux fuel (m - suc n) n

naturalMod : Nat -> Nat -> Nat
naturalMod n zero = n
naturalMod n (suc p) = mod-aux n n p

div-aux : Nat -> Nat -> Nat -> Nat
div-aux zero m n = zero
div-aux (suc fuel) m n with leb m n
... | true = zero
... | false = suc (div-aux fuel (m - suc n) n)

naturalDiv : Nat -> Nat -> Nat
naturalDiv n zero = suc n
naturalDiv n (suc p) = div-aux n n p

let-clause-1034 : Set
let-clause-1034 =
  (n m p : Nat) ->
  zero < p ->
  (x2515 x2516 : Nat) ->
  x2515 ≡
    naturalMod x2515 x2516 +
    x2516 * naturalDiv x2515 x2516
