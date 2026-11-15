(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a5:
  the number of ordered positive-integer 10-tuples whose reciprocal sum is
  one is odd. This file contains no proof.
*)

let statement =
  `ODD
     (CARD
       {t:num list |
          LENGTH t = 10 /\
          (!i:num. i < 10 ==> 0 < EL i t) /\
          sum (0..9) (\i:num. &1 / &(EL i t)) = &1})`;;
