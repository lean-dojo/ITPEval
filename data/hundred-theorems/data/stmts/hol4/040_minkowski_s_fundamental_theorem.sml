(*
  Statement-only formalization of "Minkowski's Fundamental Theorem" from
  Hundred Theorems item 040. A convex set in finite-dimensional Euclidean
  space that is symmetric about the origin and has completed Lebesgue volume
  greater than 2^n contains a nonzero integer-lattice point; for compact sets,
  equality is allowed. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open extrealTheory sigma_algebraTheory measureTheory;

val minkowski_s_fundamental_theorem =
  ``!borel_nd_measure m. !(s : ('i -> real) -> bool).
      let half_open_box =
        \a b : 'i -> real.
          {x : 'i -> real | !i. a i <= x i /\ x i < b i}
      in
      let coordinate_boxes =
        \t : ('i -> real) -> bool.
          ?a b : 'i -> real. t = half_open_box a b
      in
      let lebesgue_nd =
        (measure_space borel_nd_measure /\
         m_space borel_nd_measure = (UNIV : ('i -> real) -> bool) /\
         measurable_sets borel_nd_measure =
           subsets
             (sigma (UNIV : ('i -> real) -> bool) coordinate_boxes) /\
         (!a b : 'i -> real.
            measure borel_nd_measure (half_open_box a b) =
            Normal
              (REAL_PROD_IMAGE
                (\i. max (0 : real) (b i - a i))
                (UNIV : 'i -> bool))) /\
         measure_space m /\
         m_space m = (UNIV : ('i -> real) -> bool) /\
         measurable_sets m = subsets (completion borel_nd_measure) /\
         (!t. t IN measurable_sets borel_nd_measure ==>
              measure m t = measure borel_nd_measure t))
      in
      let convex_euclidean =
        \t.
          !x y u.
            x IN t /\ y IN t /\ 0 <= u /\ u <= 1 ==>
            (\i. (1 - u) * x i + u * y i) IN t
      in
      let origin_symmetric =
        \t. !x. x IN t ==> (\i. ~(x i)) IN t
      in
        FINITE (UNIV : 'i -> bool) /\
        lebesgue_nd /\
        convex_euclidean s /\
        origin_symmetric s /\
        Normal
          ((2 : real) pow CARD (UNIV : 'i -> bool)) <
          measure m s
        ==>
        ?u : 'i -> real.
          u IN s /\
          u <> (\i. 0) /\
          !i. ?z : int. u i = real_of_int z``;

val minkowski_s_fundamental_theorem_compact =
  ``!borel_nd_measure m. !(s : ('i -> real) -> bool).
      let half_open_box =
        \a b : 'i -> real.
          {x : 'i -> real | !i. a i <= x i /\ x i < b i}
      in
      let coordinate_boxes =
        \t : ('i -> real) -> bool.
          ?a b : 'i -> real. t = half_open_box a b
      in
      let lebesgue_nd =
        (measure_space borel_nd_measure /\
         m_space borel_nd_measure = (UNIV : ('i -> real) -> bool) /\
         measurable_sets borel_nd_measure =
           subsets
             (sigma (UNIV : ('i -> real) -> bool) coordinate_boxes) /\
         (!a b : 'i -> real.
            measure borel_nd_measure (half_open_box a b) =
            Normal
              (REAL_PROD_IMAGE
                (\i. max (0 : real) (b i - a i))
                (UNIV : 'i -> bool))) /\
         measure_space m /\
         m_space m = (UNIV : ('i -> real) -> bool) /\
         measurable_sets m = subsets (completion borel_nd_measure) /\
         (!t. t IN measurable_sets borel_nd_measure ==>
              measure m t = measure borel_nd_measure t))
      in
      let sqdist =
        \x y : 'i -> real.
          SIGMA (\i. (x i - y i) pow 2) (UNIV : 'i -> bool)
      in
      let compact_euclidean =
        \t.
          !(a : num -> 'i -> real).
            (!n. a n IN t) ==>
            ?r x.
              x IN t /\
              (!p q. p < q ==> r p < r q) /\
              !e. 0 < e ==>
                  ?N. !n. N <= n ==> sqdist (a (r n)) x < e
      in
      let convex_euclidean =
        \t.
          !x y u.
            x IN t /\ y IN t /\ 0 <= u /\ u <= 1 ==>
            (\i. (1 - u) * x i + u * y i) IN t
      in
      let origin_symmetric =
        \t. !x. x IN t ==> (\i. ~(x i)) IN t
      in
        FINITE (UNIV : 'i -> bool) /\
        lebesgue_nd /\
        compact_euclidean s /\
        convex_euclidean s /\
        origin_symmetric s /\
        Normal
          ((2 : real) pow CARD (UNIV : 'i -> bool)) <=
          measure m s
        ==>
        ?u : 'i -> real.
          u IN s /\
          u <> (\i. 0) /\
          !i. ?z : int. u i = real_of_int z``;
