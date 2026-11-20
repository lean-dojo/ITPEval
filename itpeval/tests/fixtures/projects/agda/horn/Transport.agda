{-# OPTIONS --safe #-}
module Transport where

open import Agda.Builtin.Equality using (_≡_; refl)

transport : (A B : Set) → A ≡ B → A → B
transport A .A refl proof = proof

by-equality : (A B : Set) → A ≡ B → A → B
by-equality A B equal proof = transport A B equal proof
