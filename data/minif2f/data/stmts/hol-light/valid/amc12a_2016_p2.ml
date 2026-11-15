(*
  Statement-only formalization of miniF2F valid problem amc12a_2016_p2. It concerns a real
  exponential equation with bases 10, 100, and 1000, whose asserted solution is x = 3. This
  file contains no proof.
*)

let amc12a_2016_p2 =
  `!x:real.
     exp (x * ln (&10)) * exp ((&2 * x) * ln (&100)) =
     exp (&5 * ln (&1000))
     ==> x = &3`;;
