(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q752375, "Extreme value theorem": a continuous map from a nonempty compact
  subset of a topological space into a linearly ordered topological space with
  closed lower rays attains its minimum on that subset. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory;

val q752375_linear_order_def = new_definition (
  "q752375_linear_order_def",
  ``q752375_linear_order (leq : 'a -> 'a -> bool) <=>
      (!x. leq x x) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y \/ leq y x)``);

val q752375_closed_iic_topology_def = new_definition (
  "q752375_closed_iic_topology_def",
  ``q752375_closed_iic_topology
      (top : 'a topology) (leq : 'a -> 'a -> bool) <=>
      topspace top = UNIV /\
      !a. closed_in top {x | leq x a}``);

val IsCompact_exists_isMinOn =
  ``!(topA : 'a topology) (topB : 'b topology)
      (leq : 'a -> 'a -> bool) (s : 'b set) (f : 'b -> 'a).
      q752375_linear_order leq /\
      q752375_closed_iic_topology topA leq /\
      topspace topB = UNIV /\
      compact_in topB s /\
      (?x. x IN s) /\
      continuous_map (subtopology topB s,topA) f
      ==>
      ?x.
        x IN s /\
        !y. y IN s ==> leq (f x) (f y)``;
