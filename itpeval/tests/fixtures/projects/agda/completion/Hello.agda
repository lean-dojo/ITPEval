{-# OPTIONS --safe #-}
module Hello where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

itpeval-target : true ≡ true
itpeval-target = refl
