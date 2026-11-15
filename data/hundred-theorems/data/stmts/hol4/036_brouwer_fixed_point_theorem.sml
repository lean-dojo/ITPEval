(*
  Statement-only formalization of "Brouwer Fixed Point Theorem" from Hundred Theorems item 036.
  This file contains no proof.
*)

(*
  Hundred Theorems item 036, "Brouwer Fixed Point Theorem": every continuous
  self-map of a nonempty compact convex subset of a finite-dimensional
  Euclidean real space has a fixed point in that subset. This is a
  statement-only formalization and contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val brouwer_fixed_point_theorem =
  ``!(s : ('i -> real) -> bool)
      (f : ('i -> real) -> ('i -> real)).
      let sqdist =
        \x y : 'i -> real.
          SIGMA (\k. (x k - y k) pow 2) (UNIV : 'i -> bool)
      in
      let compact_euclidean =
        \t.
          !(a : num -> 'i -> real).
            (!n. a n IN t) ==>
            ?r x.
              x IN t /\
              (!m n. m < n ==> r m < r n) /\
              !e. 0 < e ==>
                  ?N. !n. N <= n ==> sqdist (a (r n)) x < e
      in
      let convex_euclidean =
        \t.
          !x y u.
            x IN t /\ y IN t /\ 0 <= u /\ u <= 1 ==>
            (\k. (1 - u) * x k + u * y k) IN t
      in
      let continuous_on_euclidean =
        \t g.
          !x. x IN t ==>
              !e. 0 < e ==>
                  ?d. 0 < d /\
                      !y. y IN t /\ sqdist x y < d ==>
                          sqdist (g x) (g y) < e
      in
        FINITE (UNIV : 'i -> bool) /\
        compact_euclidean s /\
        convex_euclidean s /\
        (?x. x IN s) /\
        continuous_on_euclidean s f /\
        (!x. x IN s ==> f x IN s)
        ==>
        ?x. x IN s /\ f x = x``;
