(*
  Statement-only formalization of miniF2F valid problem amc12a_2019_p21:
  for z = (1 + i) / sqrt 2, the product of the sums from k = 1 to 12 of
  z^(k^2) and 1 / z^(k^2) is 36. This file contains no proof.
*)

needs "Complex/complexnumbers.ml";;

let statement =
  `!z:complex.
    z = (Cx(&1) + ii) / Cx(sqrt(&2))
    ==>
    iterate complex_add (1..12) (\k. z pow (k EXP 2)) *
    iterate complex_add (1..12) (\k. Cx(&1) / z pow (k EXP 2)) =
    Cx(&36)`;;
