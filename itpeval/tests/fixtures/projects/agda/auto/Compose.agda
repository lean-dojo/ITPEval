{-# OPTIONS --safe #-}
module Compose where

compose : {A B C : Set} → (B → C) → (A → B) → A → C
compose f g x = f (g x)
