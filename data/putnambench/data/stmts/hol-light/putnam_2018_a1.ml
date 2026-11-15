(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a1:
  classification of the positive integer ordered pairs whose reciprocals sum
  to 3/2018. This file contains no proof.
*)

let statement =
  `!a b:num.
     (0 < a /\
      0 < b /\
      (&1 / &a + &1 / &b = &3 / &2018))
     <=>
     (a = 673 /\ b = 1358114) \/
     (a = 674 /\ b = 340033) \/
     (a = 1009 /\ b = 2018) \/
     (a = 2018 /\ b = 1009) \/
     (a = 340033 /\ b = 674) \/
     (a = 1358114 /\ b = 673)`;;
