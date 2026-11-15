(*
  Statement-only formalization of miniF2F valid problem imo_1988_p6. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1988_p6: if positive natural numbers a and b
  have a * b + 1 dividing a^2 + b^2, then the resulting quotient is the
  square of a natural number. This is a statement-only formalization and
  contains no proof.
*)

let imo_1988_p6 =
  `!a b:num.
     0 < a /\
     0 < b /\
     (a * b + 1) divides (a EXP 2 + b EXP 2)
     ==> ?x:num.
           (&(x EXP 2):real) =
           &(a EXP 2 + b EXP 2) / &(a * b + 1)`;;
