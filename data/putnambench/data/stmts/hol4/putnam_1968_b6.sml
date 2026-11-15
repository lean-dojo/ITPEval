(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b6:
  no sequence of compact sets of rational numbers is cofinal under set
  inclusion among all compact sets of rational numbers. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory ratTheory realTheory real_of_ratTheory real_topologyTheory;

val putnam_1968_b6 =
  ``let compactQ =
      \S : real set.
        compact S /\
        !r : real. r IN S ==> ?q : rat. real_of_rat q = r
    in
      ~(?K : num -> real set.
          (!n : num. compactQ (K n)) /\
          !S : real set.
            compactQ S ==> ?n : num. S SUBSET K n)``;
