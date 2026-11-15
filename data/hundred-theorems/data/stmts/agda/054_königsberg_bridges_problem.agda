-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__054,
-- "Königsberg Bridges Problem": no contiguous traversal uses each of the seven bridges
-- exactly once. This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []) renaming (_∷_ to _::_)

data Bottom : Set where

data Vertex : Set where
  v0 v1 v2 v3 : Vertex

data Bridge : Set where
  b01 b02 b03 b12-first b12-second b23-first b23-second : Bridge

data Connects : Bridge -> Vertex -> Vertex -> Set where
  b01-forward  : Connects b01 v0 v1
  b01-backward : Connects b01 v1 v0
  b02-forward  : Connects b02 v0 v2
  b02-backward : Connects b02 v2 v0
  b03-forward  : Connects b03 v0 v3
  b03-backward : Connects b03 v3 v0

  b12-first-forward  : Connects b12-first v1 v2
  b12-first-backward : Connects b12-first v2 v1
  b12-second-forward  : Connects b12-second v1 v2
  b12-second-backward : Connects b12-second v2 v1

  b23-first-forward  : Connects b23-first v2 v3
  b23-first-backward : Connects b23-first v3 v2
  b23-second-forward  : Connects b23-second v2 v3
  b23-second-backward : Connects b23-second v3 v2

record Crossing : Set where
  constructor crossing
  field
    bridge : Bridge
    start : Vertex
    finish : Vertex
    follows-bridge : Connects bridge start finish

open Crossing

data Trail : List Crossing -> Set where
  empty-trail :
    Trail []
  single-crossing :
    {step : Crossing} ->
    Trail (step :: [])
  prepend-crossing :
    {first second : Crossing} ->
    {rest : List Crossing} ->
    finish first == start second ->
    Trail (second :: rest) ->
    Trail (first :: second :: rest)

data Permutation : List Bridge -> List Bridge -> Set where
  empty-permutation :
    Permutation [] []
  prepend-same :
    {left right : List Bridge} ->
    (edge : Bridge) ->
    Permutation left right ->
    Permutation (edge :: left) (edge :: right)
  swap-adjacent :
    (first second : Bridge) ->
    (rest : List Bridge) ->
    Permutation (first :: second :: rest) (second :: first :: rest)
  transitive-permutation :
    {first second third : List Bridge} ->
    Permutation first second ->
    Permutation second third ->
    Permutation first third

crossed-bridges : List Crossing -> List Bridge
crossed-bridges [] = []
crossed-bridges (step :: rest) =
  bridge step :: crossed-bridges rest

all-bridges : List Bridge
all-bridges =
  b01 ::
  b02 ::
  b03 ::
  b12-first ::
  b12-second ::
  b23-first ::
  b23-second ::
  []

konigsberg-bridges-problem : Set
konigsberg-bridges-problem =
  (crossings : List Crossing) ->
  Trail crossings ->
  Permutation all-bridges (crossed-bridges crossings) ->
  Bottom
