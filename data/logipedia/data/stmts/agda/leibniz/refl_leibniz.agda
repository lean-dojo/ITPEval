-- Statement-only formalization of Logipedia corpus artifact
-- leibniz.refl_leibniz (catalog title "leibniz.refl_leibniz"): for every
-- type and element, Leibniz equality relates that element to itself. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module refl_leibniz where

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

refl-leibniz :
  {level : Level} ->
  Set (lsuc level)
refl-leibniz {level} =
  (A : Set level) ->
  (x : A) ->
  Leibniz A x x
