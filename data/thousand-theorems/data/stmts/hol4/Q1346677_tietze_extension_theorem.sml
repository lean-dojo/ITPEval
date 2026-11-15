(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1346677, "Tietze extension theorem": a bounded continuous real-valued
  function extends along a closed embedding into a normal topological space
  with the same uniform norm. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory topologyTheory real_topologyTheory;

val q1346677_normal_space_def = new_definition (
  "q1346677_normal_space_def",
  ``q1346677_normal_space (top : 'a topology) <=>
      !s t.
        closed_in top s /\
        closed_in top t /\
        DISJOINT s t
        ==>
        ?u v.
          open_in top u /\
          open_in top v /\
          s SUBSET u /\
          t SUBSET v /\
          DISJOINT u v``);

val q1346677_closed_embedding_def = new_definition (
  "q1346677_closed_embedding_def",
  ``q1346677_closed_embedding
      (topX : 'x topology) (topY : 'y topology) (e : 'x -> 'y) <=>
      continuous_map (topX,topY) e /\
      (!x y.
        x IN topspace topX /\
        y IN topspace topX /\
        e x = e y
        ==>
        x = y) /\
      (!u.
        open_in topX u
        ==>
        ?v.
          open_in topY v /\
          u = {x | x IN topspace topX /\ e x IN v}) /\
      closed_in topY (IMAGE e (topspace topX))``);

val q1346677_bounded_continuous_def = new_definition (
  "q1346677_bounded_continuous_def",
  ``q1346677_bounded_continuous
      (top : 'a topology) (f : 'a -> real) <=>
      continuous_map (top,euclidean) f /\
      ?M : real.
        0 <= M /\
        !x. x IN topspace top ==> abs (f x) <= M``);

val q1346677_uniform_norm_def = new_definition (
  "q1346677_uniform_norm_def",
  ``q1346677_uniform_norm
      (top : 'a topology) (f : 'a -> real) (n : real) <=>
      0 <= n /\
      (!x. x IN topspace top ==> abs (f x) <= n) /\
      !m : real.
        0 <= m /\
        (!x. x IN topspace top ==> abs (f x) <= m)
        ==>
        n <= m``);

val q1346677_same_uniform_norm_def = new_definition (
  "q1346677_same_uniform_norm_def",
  ``q1346677_same_uniform_norm
      (topX : 'x topology) (topY : 'y topology)
      (f : 'x -> real) (g : 'y -> real) <=>
      ?n : real.
        q1346677_uniform_norm topX f n /\
        q1346677_uniform_norm topY g n``);

val BoundedContinuousFunction_exists_extension_norm_eq_of_isClosedEmbedding =
  ``!(topX : 'x topology) (topY : 'y topology)
      (f : 'x -> real) (e : 'x -> 'y).
      q1346677_normal_space topY /\
      q1346677_bounded_continuous topX f /\
      q1346677_closed_embedding topX topY e
      ==>
      ?g : 'y -> real.
        q1346677_bounded_continuous topY g /\
        q1346677_same_uniform_norm topX topY f g /\
        (!x. x IN topspace topX ==> g (e x) = f x)``;
