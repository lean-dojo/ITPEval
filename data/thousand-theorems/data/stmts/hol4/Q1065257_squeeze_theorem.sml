(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1065257 (thousand-theorems__hol4__Q1065257), "Squeeze theorem": for
  functions into a preordered space with its order topology, eventual lower
  and upper bounds converging to the same point force the bounded function
  to converge there. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory;

val q1065257_preorder_def = new_definition (
  "q1065257_preorder_def",
  ``q1065257_preorder (leq : 'a -> 'a -> bool) <=>
      (!x. leq x x) /\
      (!x y z. leq x y /\ leq y z ==> leq x z)``);

val q1065257_strict_def = new_definition (
  "q1065257_strict_def",
  ``q1065257_strict (leq : 'a -> 'a -> bool) x y <=>
      leq x y /\ ~leq y x``);

val q1065257_order_basic_def = new_definition (
  "q1065257_order_basic_def",
  ``q1065257_order_basic
      (leq : 'a -> 'a -> bool) (lower : 'a set) (upper : 'a set) =
      {x |
        (!l. l IN lower ==> q1065257_strict leq l x) /\
        (!u. u IN upper ==> q1065257_strict leq x u)}``);

val q1065257_order_topology_def = new_definition (
  "q1065257_order_topology_def",
  ``q1065257_order_topology
      (top : 'a topology) (leq : 'a -> 'a -> bool) <=>
      q1065257_preorder leq /\
      topspace top = UNIV /\
      (!U.
        open_in top U <=>
        !x.
          x IN U ==>
          ?lower upper.
            FINITE lower /\
            FINITE upper /\
            x IN q1065257_order_basic leq lower upper /\
            q1065257_order_basic leq lower upper SUBSET U)``);

val q1065257_filter_def = new_definition (
  "q1065257_filter_def",
  ``q1065257_filter (sets : ('b set) set) <=>
      UNIV IN sets /\
      (!s t. s IN sets /\ s SUBSET t ==> t IN sets) /\
      (!s t. s IN sets /\ t IN sets ==> s INTER t IN sets)``);

val q1065257_eventually_def = new_definition (
  "q1065257_eventually_def",
  ``q1065257_eventually (sets : ('b set) set) (p : 'b -> bool) <=>
      {x | p x} IN sets``);

val q1065257_tendsto_def = new_definition (
  "q1065257_tendsto_def",
  ``q1065257_tendsto
      (top : 'a topology) (sets : ('b set) set)
      (f : 'b -> 'a) (a : 'a) <=>
      !U.
        open_in top U /\ a IN U ==>
        q1065257_eventually sets (\x. f x IN U)``);

val tendsto_of_tendsto_of_tendsto_of_le_of_le' =
  ``!(top : 'a topology) (leq : 'a -> 'a -> bool)
      (sets : ('b set) set)
      (f : 'b -> 'a) (g : 'b -> 'a) (h : 'b -> 'a) (a : 'a).
      q1065257_order_topology top leq /\
      q1065257_filter sets /\
      q1065257_tendsto top sets g a /\
      q1065257_tendsto top sets h a /\
      q1065257_eventually sets (\x. leq (g x) (f x)) /\
      q1065257_eventually sets (\x. leq (f x) (h x))
      ==>
      q1065257_tendsto top sets f a``;
