(*
  Statement-only formalization of PutnamBench artifact putnam_1981_b2:
  the minimum value of a four-term sum of squared successive ratios over
  real numbers satisfying 1 <= r <= s <= t <= 4. This file contains no proof.
*)

let statement =
  `let feasible =
     \r s t:real.
       &1 <= r /\ r <= s /\ s <= t /\ t <= &4 in
   let objective =
     \r s t:real.
       (r - &1) pow 2 +
       (s / r - &1) pow 2 +
       (t / s - &1) pow 2 +
       (&4 / t - &1) pow 2 in
   let solution = &12 - &8 * sqrt (&2) in
   (!r s t:real.
      feasible r s t
      ==> solution <= objective r s t) /\
   (?r s t:real.
      feasible r s t /\
      objective r s t = solution)`;;
