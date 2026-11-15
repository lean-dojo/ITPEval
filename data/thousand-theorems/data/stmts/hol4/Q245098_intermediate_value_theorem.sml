(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q245098, "Intermediate value theorem": a continuous map from a closed
  interval in a dense conditionally complete linear order attains every value
  between its endpoint values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory;

val q245098_linear_order_def = new_definition (
  "q245098_linear_order_def",
  ``q245098_linear_order (leq : 'a -> 'a -> bool) <=>
      (!x. leq x x) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y \/ leq y x)``);

val q245098_strict_order_def = new_definition (
  "q245098_strict_order_def",
  ``q245098_strict_order (leq : 'a -> 'a -> bool) x y <=>
      leq x y /\ x <> y``);

val q245098_dense_order_def = new_definition (
  "q245098_dense_order_def",
  ``q245098_dense_order (leq : 'a -> 'a -> bool) <=>
      !x y.
        q245098_strict_order leq x y
        ==>
        ?z.
          q245098_strict_order leq x z /\
          q245098_strict_order leq z y``);

val q245098_conditionally_complete_linear_order_def = new_definition (
  "q245098_conditionally_complete_linear_order_def",
  ``q245098_conditionally_complete_linear_order
      (leq : 'a -> 'a -> bool) <=>
      q245098_linear_order leq /\
      (!s : 'a set.
        ((?x. x IN s) /\
         (?bound. !x. x IN s ==> leq x bound))
        ==>
        ?sup.
          (!x. x IN s ==> leq x sup) /\
          !z. (!x. x IN s ==> leq x z) ==> leq sup z) /\
      (!s : 'a set.
        ((?x. x IN s) /\
         (?bound. !x. x IN s ==> leq bound x))
        ==>
        ?inf.
          (!x. x IN s ==> leq inf x) /\
          !z. (!x. x IN s ==> leq z x) ==> leq z inf)``);

val q245098_order_basic_def = new_definition (
  "q245098_order_basic_def",
  ``q245098_order_basic
      (leq : 'a -> 'a -> bool) (lower : 'a set) (upper : 'a set) =
      {x |
        (!l. l IN lower ==> q245098_strict_order leq l x) /\
        (!u. u IN upper ==> q245098_strict_order leq x u)}``);

val q245098_order_topology_def = new_definition (
  "q245098_order_topology_def",
  ``q245098_order_topology
      (top : 'a topology) (leq : 'a -> 'a -> bool) <=>
      topspace top = UNIV /\
      !U.
        open_in top U <=>
        !x.
          x IN U ==>
          ?lower upper.
            FINITE lower /\
            FINITE upper /\
            x IN q245098_order_basic leq lower upper /\
            q245098_order_basic leq lower upper SUBSET U``);

val q245098_order_closed_topology_def = new_definition (
  "q245098_order_closed_topology_def",
  ``q245098_order_closed_topology
      (top : 'a topology) (leq : 'a -> 'a -> bool) <=>
      topspace top = UNIV /\
      !x y.
        ~leq x y
        ==>
        ?U V.
          open_in top U /\
          open_in top V /\
          x IN U /\
          y IN V /\
          !u v. u IN U /\ v IN V ==> ~leq u v``);

val q245098_continuous_on_def = new_definition (
  "q245098_continuous_on_def",
  ``q245098_continuous_on
      (topA : 'a topology) (topD : 'd topology)
      (f : 'a -> 'd) (s : 'a set) <=>
      !x.
        x IN s ==>
        !V.
          open_in topD V /\ f x IN V
          ==>
          ?U.
            open_in topA U /\
            x IN U /\
            !y. y IN s /\ y IN U ==> f y IN V``);

val intermediate_value_Icc =
  ``!(topA : 'a topology) (topD : 'd topology)
      (leA : 'a -> 'a -> bool) (leD : 'd -> 'd -> bool)
      (a : 'a) (b : 'a) (f : 'a -> 'd).
      q245098_conditionally_complete_linear_order leA /\
      q245098_dense_order leA /\
      q245098_order_topology topA leA /\
      q245098_linear_order leD /\
      q245098_order_closed_topology topD leD /\
      leA a b /\
      q245098_continuous_on topA topD f
        {x | leA a x /\ leA x b}
      ==>
      !y.
        leD (f a) y /\ leD y (f b)
        ==>
        ?x.
          leA a x /\ leA x b /\
          f x = y``;
