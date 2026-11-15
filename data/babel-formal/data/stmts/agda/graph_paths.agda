-- Statement-only formalization of the Babel-formal topic graph_paths. This file contains no
-- proof.

module graph_paths where

open import Agda.Primitive using (Level; lsuc)

Edge : forall {l : Level} -> Set l -> Set (lsuc l)
Edge {l} V = V -> V -> Set l

data Path {l : Level} {V : Set l} (E : Edge V) : V -> V -> Set l where
  nil  : (v : V) -> Path E v v
  step : forall {u v w : V} -> Path E u v -> E v w -> Path E u w

Erev : forall {l : Level} {V : Set l} -> Edge V -> Edge V
Erev E x y = E y x

Undirected : forall {l : Level} {V : Set l} -> Edge V -> Set l
Undirected {V = V} E = (x y : V) -> E x y -> E y x

module GraphPathStatements
  {l : Level} {V : Set l} (E : Edge V) where

  path-refl : Set l
  path-refl =
    (v : V) -> Path E v v

  path-append-right : Set l
  path-append-right =
    (v w : V) -> Path E v w ->
    (u : V) -> Path E u v -> Path E u w

  path-trans : Set l
  path-trans =
    (u v w : V) ->
    Path E u v -> Path E v w -> Path E u w

  reverse-path : Set l
  reverse-path =
    (u v : V) ->
    Undirected E -> Path E u v -> Path E v u

  concat-edge-right : Set l
  concat-edge-right =
    (u v w : V) ->
    Path E u v -> E v w -> Path E u w

  concat : Set l
  concat =
    (u v w : V) ->
    Path E u v -> Path E v w -> Path E u w

  edge-path : Set l
  edge-path =
    (u v : V) -> E u v -> Path E u v

  concat-edge-left : Set l
  concat-edge-left =
    (u v w : V) ->
    E u v -> Path E v w -> Path E u w

  concat3 : Set l
  concat3 =
    (u v w t : V) ->
    Path E u v -> Path E v w -> Path E w t -> Path E u t

  reverse-in-Erev : Set l
  reverse-in-Erev =
    (u v : V) -> Path E u v -> Path (Erev E) v u

  cycle-refl : Set l
  cycle-refl =
    (v w : V) ->
    Path E v w -> Path E w v -> Path E v v
