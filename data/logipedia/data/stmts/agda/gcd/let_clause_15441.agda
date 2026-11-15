-- Statement-only formalization of Logipedia corpus artifact
-- gcd.let_clause_15441 (catalog title "gcd.let_clause_15441"): a local
-- natural-number equality step for the recursive auxiliary greatest common
-- divisor, commuting the factors in the second truncated difference. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-15441 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infixr 1 _∨_
infix 4 _≤_ _<_ Divides

data ⊥ : Set where

data _∨_ (A B : Set) : Set where
  left : A -> A ∨ B
  right : B -> A ∨ B

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_<_ : Nat -> Nat -> Set
m < n = suc m ≤ n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero n m = n
mod-aux (suc p) n m with leb n m
... | true = n
... | false = mod-aux p (n - suc m) m

naturalMod : Nat -> Nat -> Nat
naturalMod n zero = n
naturalMod n (suc m) = mod-aux n n m

dividesb : Nat -> Nat -> Bool
dividesb n m = eqb (naturalMod m n) zero

gcd-aux : Nat -> Nat -> Nat -> Nat
gcd-aux zero m n = m
gcd-aux (suc p) m n with dividesb n m
... | true = n
... | false = gcd-aux p n (naturalMod m n)

let-clause-15441 : Set
let-clause-15441 =
  (p q : Nat) ->
  ((m n : Nat) ->
    zero < n ->
    n ≤ m ->
    n ≤ q ->
    Σ Nat (\ a ->
      Σ Nat (\ b ->
        ((a * n) - (b * m) ≡ gcd-aux q m n) ∨
        ((b * m) - (a * n) ≡ gcd-aux q m n)))) ->
  (m n : Nat) ->
  zero < n ->
  n ≤ m ->
  n ≤ suc q ->
  (Divides n m -> ⊥) ->
  (a : Nat) ->
  Σ Nat (\ b ->
    ((a * naturalMod m n) - (b * n) ≡
      gcd-aux q n (naturalMod m n)) ∨
    ((b * n) - (a * naturalMod m n) ≡
      gcd-aux q n (naturalMod m n))) ->
  (b : Nat) ->
  (((a * naturalMod m n) - (b * n) ≡
      gcd-aux q n (naturalMod m n)) ∨
    ((b * n) - (a * naturalMod m n) ≡
      gcd-aux q n (naturalMod m n))) ->
  ((b * n) - (a * naturalMod m n) ≡
    gcd-aux q n (naturalMod m n)) ->
  (n * b) - (a * naturalMod m n) ≡
    gcd-aux q n (naturalMod m n)
