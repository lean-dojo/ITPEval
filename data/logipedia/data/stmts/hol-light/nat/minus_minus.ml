(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_minus,
  catalog title "nat.minus_minus": for natural numbers p <= m <= n, adding p
  to the truncated difference n - m equals the truncated difference
  n - (m - p). This file contains no proof.
*)

let statement =
  `!n m p:num.
     p <= m ==> m <= n ==> p + (n - m) = n - (m - p)`;;
