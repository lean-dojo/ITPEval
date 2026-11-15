(*
  Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_bc:
  distributing a natural-number power across a product indexed from zero up
  to the truncated difference c - b. This file contains no proof.
*)

let statement =
  `!a b c:num f:num->num.
     a EXP (c - b) *
       nproduct {i | i < c - b} (\i. f (i + b)) =
     nproduct {i | i < c - b} (\i. a * f (i + b))`;;
