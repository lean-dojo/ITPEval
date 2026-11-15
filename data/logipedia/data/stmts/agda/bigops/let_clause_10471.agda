-- Statement-only formalization of the Logipedia corpus artifact
-- bigops.let_clause_10471: a nested big-operator induction context concluding
-- the natural-number quotient and remainder decomposition; this file contains no proof.
{-# OPTIONS --safe #-}

module let-clause-10471 where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ _≤_
infixr 3 _∧_

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < suc n
  succ<succ : {m n : Nat} -> m < n -> suc m < suc n

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

record _∧_ (A B : Set) : Set where
  field
    first : A
    second : B

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

bigop :
  {level : Level} ->
  {H : Set level} ->
  Nat ->
  (Nat -> Bool) ->
  H ->
  (H -> H -> H) ->
  (Nat -> H) ->
  H
bigop zero p nil op f = nil
bigop (suc n) p nil op f with p n
... | true = op (f n) (bigop n p nil op f)
... | false = bigop n p nil op f

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero m n = m
mod-aux (suc fuel) m n with leb m n
... | true = m
... | false = mod-aux fuel (m - suc n) n

mod : Nat -> Nat -> Nat
mod n zero = n
mod n (suc p) = mod-aux n n p

div-aux : Nat -> Nat -> Nat -> Nat
div-aux zero m n = zero
div-aux (suc fuel) m n with leb m n
... | true = zero
... | false = suc (div-aux fuel (m - suc n) n)

div : Nat -> Nat -> Nat
div n zero = suc n
div n (suc p) = div-aux n n p

same :
  (n1 : Nat) ->
  (p1 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
same n1 p1 f1 f2 h =
  (j : Nat) ->
  j < n1 ->
  p1 j ≡ true ->
  f1 j ≡ f2 (h j)

sub-hk :
  (h k : Nat -> Nat) ->
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  Set
sub-hk h k n1 n2 p1 p2 f1 f2 =
  (j : Nat) ->
  j < n1 ->
  p1 j ≡ true ->
  (h j < n2 ∧ p2 (h j) ≡ true) ∧ k (h j) ≡ j

full :
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  (h k : Nat -> Nat) ->
  Set
full n1 n2 p1 p2 f1 f2 h k =
  (same n1 p1 f1 f2 h ∧ sub-hk h k n1 n2 p1 p2 f1 f2) ∧
  sub-hk k h n2 n1 p2 p1 f2 f1

partial :
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  (h k : Nat -> Nat) ->
  Set
partial n1 n2 p1 p2 f1 f2 h k =
  same n1 p1 f1 f2 h ∧ sub-hk h k n1 n2 p1 p2 f1 f2

iso :
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  Set
iso n1 n2 p1 p2 f1 f2 =
  Σ (Nat -> Nat) (\ h ->
    Σ (Nat -> Nat) (\ k ->
      full n1 n2 p1 p2 f1 f2 h k))

induction-hypothesis :
  (n1 : Nat) ->
  (p1 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  (h k : Nat -> Nat) ->
  Nat ->
  Set
induction-hypothesis n1 p1 f1 f2 h k m =
  (f : Nat -> Bool) ->
  zero ≤ n1 ->
  sub-hk h k zero m p1 f f1 f2 ->
  sub-hk k h m zero f p1 f2 f1 ->
  bigop zero p1 1 _*_ f1 ≡ bigop m f 1 _*_ f2

let-clause-10471 : Set
let-clause-10471 =
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  iso n1 n2 p1 p2 f1 f2 ->
  (h : Nat -> Nat) ->
  Σ (Nat -> Nat) (\ k -> full n1 n2 p1 p2 f1 f2 h k) ->
  (k : Nat -> Nat) ->
  full n1 n2 p1 p2 f1 f2 h k ->
  partial n1 n2 p1 p2 f1 f2 h k ->
  same n1 p1 f1 f2 h ->
  (i m : Nat) ->
  induction-hypothesis n1 p1 f1 f2 h k m ->
  (p20 : Nat -> Bool) ->
  zero ≤ n1 ->
  sub-hk h k zero (suc m) p1 p20 f1 f2 ->
  sub-hk k h (suc m) zero p20 p1 f2 f1 ->
  (x2571 x2572 : Nat) ->
  x2571 ≡ x2572 * div x2571 x2572 + mod x2571 x2572
