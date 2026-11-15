(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527166 (thousand-theorems__hol4__Q3527166), "Steinhaus theorem": every
  measurable set of positive inner-regular Haar measure in a locally compact
  topological group has a quotient set that is a neighborhood of the identity.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory extrealTheory topologyTheory sigma_algebraTheory;
open measureTheory borelTheory;

val q3527166_group_def = new_definition (
  "q3527166_group_def",
  ``q3527166_group
      (one : 'g) (mul : 'g -> 'g -> 'g) (inv : 'g -> 'g) <=>
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul one x = x /\ mul x one = x) /\
      (!x. mul (inv x) x = one /\ mul x (inv x) = one)``);

val q3527166_topological_group_def = new_definition (
  "q3527166_topological_group_def",
  ``q3527166_topological_group
      (top : 'g topology) (mul : 'g -> 'g -> 'g) (inv : 'g -> 'g) <=>
      topspace top = UNIV /\
      (!x y u.
        open_in top u /\ mul x y IN u ==>
        ?v w.
          open_in top v /\ x IN v /\
          open_in top w /\ y IN w /\
          !x' y'. x' IN v /\ y' IN w ==> mul x' y' IN u) /\
      continuous_map (top,top) inv``);

val q3527166_borel_measure_def = new_definition (
  "q3527166_borel_measure_def",
  ``q3527166_borel_measure (top : 'g topology) (m : 'g m_space) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m = subsets (general_borel top)``);

val q3527166_outer_measure_def = new_definition (
  "q3527166_outer_measure_def",
  ``q3527166_outer_measure (m : 'g m_space) (s : 'g set) =
      inf
        {r : extreal |
          ?t : 'g set.
            s SUBSET t /\
            t IN measurable_sets m /\
            measure m t = r}``);

val q3527166_neighborhood_def = new_definition (
  "q3527166_neighborhood_def",
  ``q3527166_neighborhood
      (top : 'g topology) (x : 'g) (s : 'g set) <=>
      ?u. open_in top u /\ x IN u /\ u SUBSET s``);

val q3527166_locally_compact_def = new_definition (
  "q3527166_locally_compact_def",
  ``q3527166_locally_compact (top : 'g topology) <=>
      !x n.
        q3527166_neighborhood top x n ==>
        ?k.
          q3527166_neighborhood top x k /\
          k SUBSET n /\
          compact_in top k``);

val q3527166_haar_measure_def = new_definition (
  "q3527166_haar_measure_def",
  ``q3527166_haar_measure
      (top : 'g topology) (mul : 'g -> 'g -> 'g) (m : 'g m_space) <=>
      (!a s.
        q3527166_outer_measure m {x | mul a x IN s} =
        q3527166_outer_measure m s) /\
      (!k.
        compact_in top k ==>
        q3527166_outer_measure m k <> PosInf) /\
      (!u.
        open_in top u /\ u <> {} ==>
        0 < q3527166_outer_measure m u)``);

val q3527166_inner_regular_def = new_definition (
  "q3527166_inner_regular_def",
  ``q3527166_inner_regular (top : 'g topology) (m : 'g m_space) <=>
      !u.
        u IN measurable_sets m ==>
        !r : extreal.
          r < q3527166_outer_measure m u ==>
          ?k.
            k SUBSET u /\
            compact_in top k /\
            r < q3527166_outer_measure m k``);

val q3527166_div_set_def = new_definition (
  "q3527166_div_set_def",
  ``q3527166_div_set
      (mul : 'g -> 'g -> 'g) (inv : 'g -> 'g) (s : 'g set) =
      {z | ?x y. x IN s /\ y IN s /\ z = mul x (inv y)}``);

val div_mem_nhds_one_of_haar_pos =
  ``!(one : 'g) (mul : 'g -> 'g -> 'g) (inv : 'g -> 'g)
      (top : 'g topology) (m : 'g m_space) (e : 'g set).
      q3527166_group one mul inv /\
      q3527166_topological_group top mul inv /\
      q3527166_borel_measure top m /\
      q3527166_locally_compact top /\
      q3527166_haar_measure top mul m /\
      q3527166_inner_regular top m /\
      e IN measurable_sets m /\
      0 < q3527166_outer_measure m e
      ==>
      q3527166_neighborhood top one
        (q3527166_div_set mul inv e)``;
