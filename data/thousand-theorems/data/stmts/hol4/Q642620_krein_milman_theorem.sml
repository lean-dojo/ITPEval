(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q642620 (thousand-theorems__hol4__Q642620), "Krein–Milman theorem":
  every compact convex subset of a real Hausdorff locally convex topological
  vector space is the closure of the convex hull of its extreme points.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory topologyTheory real_topologyTheory;

val closure_convexHull_extremePoints =
  ``!(vzero : 'e) (vadd : 'e -> 'e -> 'e) (vneg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (top : 'e topology) (s : 'e set).
      let q642620_add_comm_group = (
        (!x y. vadd x y = vadd y x) /\
        (!x y z. vadd (vadd x y) z = vadd x (vadd y z)) /\
        (!x. vadd x vzero = x) /\
        (!x. vadd x (vneg x) = vzero))
      in
      let q642620_real_module = (
        (!x. smul 1 x = x) /\
        (!a b x. smul (a * b) x = smul a (smul b x)) /\
        (!a b x. smul (a + b) x = vadd (smul a x) (smul b x)) /\
        (!a x y. smul a (vadd x y) = vadd (smul a x) (smul a y)))
      in
      let q642620_hausdorff = (
        !x y.
          x <> y ==>
          ?u v.
            open_in top u /\ open_in top v /\
            x IN u /\ y IN v /\ DISJOINT u v)
      in
      let q642620_continuous_vadd = (
        !x y u.
          open_in top u /\ vadd x y IN u ==>
          ?v w.
            open_in top v /\ x IN v /\
            open_in top w /\ y IN w /\
            !x' y'. x' IN v /\ y' IN w ==> vadd x' y' IN u)
      in
      let q642620_continuous_real_smul = (
        !a x u.
          open_in top u /\ smul a x IN u ==>
          ?v w.
            open_in euclidean v /\ a IN v /\
            open_in top w /\ x IN w /\
            !a' x'. a' IN v /\ x' IN w ==> smul a' x' IN u)
      in
      let q642620_topological_add_group =
        (q642620_continuous_vadd /\ continuous_map (top,top) vneg)
      in
      let q642620_convex = (
        \(s : 'e set).
          !x y a b.
            x IN s /\ y IN s /\
            0 <= a /\ 0 <= b /\ a + b = 1 ==>
            vadd (smul a x) (smul b y) IN s)
      in
      let q642620_convex_hull = (
        \(a : 'e set).
          {x : 'e |
            !t : 'e set.
              a SUBSET t /\ q642620_convex t ==> x IN t})
      in
      let q642620_neighborhood = (
        \(x : 'e) (a : 'e set).
          ?u.
            open_in top u /\ x IN u /\ u SUBSET a)
      in
      let q642620_extreme_points = (
        \(a : 'e set).
          {x : 'e |
            x IN a /\
            !x1 x2.
              x1 IN a /\ x2 IN a /\
              (?r1 r2.
                0 < r1 /\ 0 < r2 /\ r1 + r2 = 1 /\
                vadd (smul r1 x1) (smul r2 x2) = x)
              ==>
              x1 = x})
      in
      let q642620_locally_convex = (
        !x u.
          q642620_neighborhood x u ==>
          ?a.
            q642620_neighborhood x a /\
            q642620_convex a /\
            a SUBSET u)
      in
        q642620_add_comm_group /\
        q642620_real_module /\
        topspace top = UNIV /\
        q642620_hausdorff /\
        q642620_topological_add_group /\
        q642620_continuous_real_smul /\
        q642620_locally_convex /\
        compact_in top s /\
        q642620_convex s
        ==>
        top closure_of
          (q642620_convex_hull (q642620_extreme_points s)) = s``;
