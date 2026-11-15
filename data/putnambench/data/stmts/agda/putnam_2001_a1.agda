-- Statement-only formalization of PutnamBench corpus artifact putnam_2001_a1
-- (putnambench__agda__putnam_2001_a1): a binary operation satisfying
-- (a * b) * a = b also satisfies a * (b * a) = b. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)

putnam-2001-a1 : Set1
putnam-2001-a1 =
  (A : Set) ->
  (op : A -> A -> A) ->
  ((a b : A) -> op (op a b) a == b) ->
  (a b : A) -> op a (op b a) == b
