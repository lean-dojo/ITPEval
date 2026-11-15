(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a1:
  the three-dimensional Lebesgue volume of the region satisfying
  (x^2 + y^2 + z^2 + 8)^2 <= 36(x^2 + y^2) is 6*pi^2. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val putnam_2006_a1 =
  ``measure
      (prod_measure_space
        (prod_measure_space lebesgue lebesgue)
        lebesgue)
      {p : (real # real) # real |
        let x = FST (FST p) in
        let y = SND (FST p) in
        let z = SND p in
          (x pow 2 + y pow 2 + z pow 2 + 8) pow 2 <=
            36 * (x pow 2 + y pow 2)} =
    Normal (6 * pi pow 2)``;
