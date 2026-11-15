(*
  Statement-only formalization of miniF2F valid problem aime_1984_p15. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val aime_1984_p15 =
  ``!x y z w : real.
      x pow 2 / (2 pow 2 - 1) +
        y pow 2 / (2 pow 2 - 3 pow 2) +
        z pow 2 / (2 pow 2 - 5 pow 2) +
        w pow 2 / (2 pow 2 - 7 pow 2) = 1 /\
      x pow 2 / (4 pow 2 - 1) +
        y pow 2 / (4 pow 2 - 3 pow 2) +
        z pow 2 / (4 pow 2 - 5 pow 2) +
        w pow 2 / (4 pow 2 - 7 pow 2) = 1 /\
      x pow 2 / (6 pow 2 - 1) +
        y pow 2 / (6 pow 2 - 3 pow 2) +
        z pow 2 / (6 pow 2 - 5 pow 2) +
        w pow 2 / (6 pow 2 - 7 pow 2) = 1 /\
      x pow 2 / (8 pow 2 - 1) +
        y pow 2 / (8 pow 2 - 3 pow 2) +
        z pow 2 / (8 pow 2 - 5 pow 2) +
        w pow 2 / (8 pow 2 - 7 pow 2) = 1
      ==>
      x pow 2 + y pow 2 + z pow 2 + w pow 2 = 36``;
