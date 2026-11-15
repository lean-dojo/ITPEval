(*
  Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_l,
  catalog title "sigma_pi.exp_pi_l": multiplying the product of the first n
  values of a natural-number function by a^n equals multiplying each value by
  a before taking the product. This file contains no proof.
*)

let statement =
  `!n a:num f:num->num.
     a EXP n * nproduct {i | i < n} (\i. f i) =
     nproduct {i | i < n} (\i. a * f i)`;;
