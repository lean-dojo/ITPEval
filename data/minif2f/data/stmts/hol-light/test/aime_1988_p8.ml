(*
  Statement-only formalization of miniF2F artifact aime_1988_p8: a functional equation
  on positive natural-number inputs with real values. This file contains no proof.
*)

let statement = `!f:num->num->real.
  ((!x. 0 < x ==> f x x = &x) /\
   (!x y. 0 < x /\ 0 < y ==> f x y = f y x) /\
   (!x y. 0 < x /\ 0 < y ==>
      (&x + &y) * f x y = &y * f x (x + y)))
  ==> f 14 52 = &364`;;
