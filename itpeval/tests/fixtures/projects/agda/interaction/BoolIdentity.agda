{-# OPTIONS --safe #-}
module BoolIdentity where

open import Agda.Builtin.Bool

ident : Bool → Bool
ident x = x
