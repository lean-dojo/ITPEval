(*
  Statement-only formalization of miniF2F valid problem imo_1987_p6. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1987_p6: for the natural-number quadratic
  f(k) = k^2 + k + p, primality through sqrt(p / 3) implies primality
  through p - 2. This is a statement-only formalization and contains no proof.
*)

let imo_1987_p6 =
  `!p:num. !f:num->num.
     (!x:num. f x = x EXP 2 + x + p) /\
     (!k:num. &k <= sqrt (&p / &3) ==> prime (f k))
     ==> !i:num. i <= p - 2 ==> prime (f i)`;;
