(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a5:
  the sharp supremum of the absolute derivative at zero among real quadratic
  polynomials bounded in absolute value by 1 on [0,1]. This file contains no proof.
*)

let statement =
  `let admissible =
     \a b c:real.
       ~(a = &0) /\
       (!x:real.
          &0 <= x /\ x <= &1
          ==> abs (a * x pow 2 + b * x + c) <= &1) in
   (?a b c:real. admissible a b c /\ abs b = &8) /\
   (!a b c:real. admissible a b c ==> abs b <= &8)`;;
