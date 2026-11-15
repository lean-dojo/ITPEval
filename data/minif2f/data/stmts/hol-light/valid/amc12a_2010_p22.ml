(*
  Statement-only formalization of miniF2F valid problem amc12a_2010_p22. This file contains no
  proof.
*)

let amc12a_2010_p22 =
  `!x:real.
     &49 <= sum (1..119) (\k:num. abs (&k * x - &1))`;;
