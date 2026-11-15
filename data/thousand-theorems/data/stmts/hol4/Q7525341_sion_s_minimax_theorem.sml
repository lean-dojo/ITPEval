(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7525341 (thousand-theorems__hol4__Q7525341), "Sion's minimax theorem":
  for a lower-semicontinuous quasiconvex / upper-semicontinuous quasiconcave
  function on convex subsets of real topological vector spaces, with the
  first subset nonempty and compact, the specified infimum of row suprema
  equals the specified supremum of column infima. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory topologyTheory real_topologyTheory;

val q7525341_dense_linear_order_def = new_definition (
  "q7525341_dense_linear_order_def",
  ``q7525341_dense_linear_order (leq : 'b -> 'b -> bool) <=>
      (!a. leq a a) /\
      (!a b c. leq a b /\ leq b c ==> leq a c) /\
      (!a b. leq a b /\ leq b a ==> a = b) /\
      (!a b. leq a b \/ leq b a) /\
      (!a b.
        leq a b /\ a <> b ==>
        ?c. leq a c /\ a <> c /\ leq c b /\ c <> b)``);

val q7525341_real_topological_vector_space_def = new_definition (
  "q7525341_real_topological_vector_space_def",
  ``q7525341_real_topological_vector_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (top : 'e topology) <=>
      topspace top = UNIV /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x y u.
        open_in top u /\ add x y IN u ==>
        ?v w.
          open_in top v /\ x IN v /\
          open_in top w /\ y IN w /\
          !x' y'. x' IN v /\ y' IN w ==> add x' y' IN u) /\
      (!x u.
        open_in top u /\ neg x IN u ==>
        ?v.
          open_in top v /\ x IN v /\
          !x'. x' IN v ==> neg x' IN u) /\
      (!a x u.
        open_in top u /\ smul a x IN u ==>
        ?v w.
          open_in euclidean v /\ a IN v /\
          open_in top w /\ x IN w /\
          !a' x'. a' IN v /\ x' IN w ==> smul a' x' IN u)``);

val q7525341_convex_def = new_definition (
  "q7525341_convex_def",
  ``q7525341_convex
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (s : 'e set) <=>
      !x y a b.
        x IN s /\ y IN s /\
        0 <= a /\ 0 <= b /\ a + b = 1 ==>
        add (smul a x) (smul b y) IN s``);

val q7525341_lower_semicontinuous_on_def = new_definition (
  "q7525341_lower_semicontinuous_on_def",
  ``q7525341_lower_semicontinuous_on
      (top : 'e topology) (leq : 'b -> 'b -> bool)
      (s : 'e set) (g : 'e -> 'b) <=>
      !x.
        x IN s ==>
        !b.
          leq b (g x) /\ b <> g x ==>
          ?u.
            open_in top u /\ x IN u /\
            !z.
              z IN s /\ z IN u ==>
              leq b (g z) /\ b <> g z``);

val q7525341_upper_semicontinuous_on_def = new_definition (
  "q7525341_upper_semicontinuous_on_def",
  ``q7525341_upper_semicontinuous_on
      (top : 'e topology) (leq : 'b -> 'b -> bool)
      (s : 'e set) (g : 'e -> 'b) <=>
      !x.
        x IN s ==>
        !b.
          leq (g x) b /\ g x <> b ==>
          ?u.
            open_in top u /\ x IN u /\
            !z.
              z IN s /\ z IN u ==>
              leq (g z) b /\ g z <> b``);

val q7525341_quasiconvex_on_def = new_definition (
  "q7525341_quasiconvex_on_def",
  ``q7525341_quasiconvex_on
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (leq : 'b -> 'b -> bool) (s : 'e set) (g : 'e -> 'b) <=>
      !r.
        q7525341_convex add smul
          {x | x IN s /\ leq (g x) r}``);

val q7525341_quasiconcave_on_def = new_definition (
  "q7525341_quasiconcave_on_def",
  ``q7525341_quasiconcave_on
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (leq : 'b -> 'b -> bool) (s : 'e set) (g : 'e -> 'b) <=>
      !r.
        q7525341_convex add smul
          {x | x IN s /\ leq r (g x)}``);

val q7525341_is_lub_def = new_definition (
  "q7525341_is_lub_def",
  ``q7525341_is_lub
      (leq : 'b -> 'b -> bool) (p : 'b -> bool) (a : 'b) <=>
      (!z. p z ==> leq z a) /\
      (!u. (!z. p z ==> leq z u) ==> leq a u)``);

val q7525341_is_glb_def = new_definition (
  "q7525341_is_glb_def",
  ``q7525341_is_glb
      (leq : 'b -> 'b -> bool) (p : 'b -> bool) (a : 'b) <=>
      (!z. p z ==> leq a z) /\
      (!l. (!z. p z ==> leq l z) ==> leq l a)``);

val sion_minimax =
  ``!(zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : real -> 'e -> 'e) (topE : 'e topology)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : real -> 'f -> 'f) (topF : 'f topology)
      (leq : 'b -> 'b -> bool)
      (X : 'e set) (Y : 'f set) (f : 'e -> 'f -> 'b)
      (sup_y : 'e -> 'b) (inf_sup : 'b)
      (inf_x : 'f -> 'b) (sup_inf : 'b).
      q7525341_dense_linear_order leq /\
      q7525341_real_topological_vector_space
        zeroE addE negE smulE topE /\
      q7525341_real_topological_vector_space
        zeroF addF negF smulF topF /\
      (?x. x IN X) /\
      compact_in topE X /\
      q7525341_convex addE smulE X /\
      q7525341_convex addF smulF Y /\
      (!y.
        y IN Y ==>
        q7525341_lower_semicontinuous_on
          topE leq X (\x. f x y)) /\
      (!y.
        y IN Y ==>
        q7525341_quasiconvex_on
          addE smulE leq X (\x. f x y)) /\
      (!x.
        x IN X ==>
        q7525341_upper_semicontinuous_on
          topF leq Y (f x)) /\
      (!x.
        x IN X ==>
        q7525341_quasiconcave_on
          addF smulF leq Y (f x)) /\
      (!x.
        x IN X ==>
        q7525341_is_lub leq
          (\z. ?y. y IN Y /\ z = f x y)
          (sup_y x)) /\
      q7525341_is_glb leq
        (\z. ?x. x IN X /\ z = sup_y x)
        inf_sup /\
      (!y.
        y IN Y ==>
        q7525341_is_glb leq
          (\z. ?x. x IN X /\ z = f x y)
          (inf_x y)) /\
      q7525341_is_lub leq
        (\z. ?y. y IN Y /\ z = inf_x y)
        sup_inf
      ==>
      inf_sup = sup_inf``;
