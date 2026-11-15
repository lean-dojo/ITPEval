-- Statement-only formalization of miniF2F valid problem mathd_algebra_144. This file contains
-- no proof.

module mathd-algebra-144 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _-_; _<_)

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

mathd-algebra-144 : Set
mathd-algebra-144 =
  (a b c d : Nat) →
  NatLess zero a →
  NatLess zero b →
  NatLess zero c →
  NatLess zero d →
  c - b ≡ d →
  b - a ≡ d →
  a + b + c ≡ 60 →
  NatLess c (a + b) →
  NatLess d 10
