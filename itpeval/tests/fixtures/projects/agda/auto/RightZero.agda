{-# OPTIONS --safe #-}
module RightZero where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

cong-suc : {m n : Nat} → m ≡ n → suc m ≡ suc n
cong-suc refl = refl

plus-zero : (n : Nat) → n + zero ≡ n
plus-zero zero = refl
plus-zero (suc n) = cong-suc (plus-zero n)

right-zero : (n : Nat) → n + zero ≡ n
right-zero n = plus-zero n
