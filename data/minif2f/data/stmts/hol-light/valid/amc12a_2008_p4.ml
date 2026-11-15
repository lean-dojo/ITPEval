(*
  Statement-only formalization of miniF2F valid problem amc12a_2008_p4:
  the real product from k = 1 through 501 of (4*k + 4) / (4*k) equals 502.
  This file contains no proof.
*)

let statement =
  `product (1..501) (\k:num. (&4 * &k + &4) / (&4 * &k)) = &502`;;
