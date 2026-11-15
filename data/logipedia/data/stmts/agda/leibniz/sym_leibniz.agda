-- Statement-only formalization of Logipedia corpus artifact
-- leibniz.sym_leibniz (catalog title "leibniz.sym_leibniz"): Leibniz
-- equality is symmetric for every type and pair of elements. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module sym_leibniz where

open import Agda.Primitive using (Level; lsuc)

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

sym-leibniz :
  {level : Level} ->
  Set (lsuc level)
sym-leibniz {level} =
  (A : Set level) ->
  (x y : A) ->
  Leibniz A x y ->
  Leibniz A y x
