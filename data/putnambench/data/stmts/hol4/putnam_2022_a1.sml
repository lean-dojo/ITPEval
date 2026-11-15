(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a1:
  the real lines y = a*x + b that intersect y = ln(1+x^2) in exactly one
  point are characterized by explicit slope and intercept conditions. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;

val putnam_2022_a1 =
  ``let solution =
      \p : real # real.
        let a = FST p
        in
        let b = SND p
        in
          (a = 0 /\ b = 0) \/
          1 <= abs a \/
          (0 < abs a /\ abs a < 1 /\
           (let rm = (1 - sqrt (1 - a pow 2)) / a
            in
            let rp = (1 + sqrt (1 - a pow 2)) / a
            in
              b < ln (1 + rm pow 2) - a * rm \/
              b > ln (1 + rp pow 2) - a * rp))
    in
      {p : real # real |
         ?!x : real.
           FST p * x + SND p = ln (1 + x pow 2)} =
      {p : real # real | solution p}``;
