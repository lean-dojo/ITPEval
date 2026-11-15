-- Statement-only formalization of Logipedia corpus artifact bigops.mk_Aop
-- (catalog title "bigops.mk_Aop"): left and right identity and associativity
-- of an arbitrary binary operation imply the source's opaque Aop predicate
-- for its neutral element. This file contains no proof.

{-# OPTIONS --safe #-}

module mk_Aop where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

module Statement
  {level : Level}
  (Aop : (A : Set level) -> A -> Set level) where

  mk-Aop :
    Set (lsuc level)
  mk-Aop =
    (A : Set level) ->
    (nil : A) ->
    (op : A -> A -> A) ->
    ((a : A) -> op nil a ≡ a) ->
    ((a : A) -> op a nil ≡ a) ->
    ((a b c : A) -> op a (op b c) ≡ op (op a b) c) ->
    Aop A nil
