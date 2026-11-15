(*
  Statement-only formalization of miniF2F test problem mathd_algebra_459. This file contains no
  proof.
*)

let statement =
  `let is_rat = \x:real.
     ?p:int q:num. ~(q = 0) /\ x = real_of_int p / &q in
   !a b c d:real.
     is_rat a /\ is_rat b /\ is_rat c /\ is_rat d /\
     &3 * a = b + c + d /\
     &4 * b = a + c + d /\
     &2 * c = a + b + d /\
     &8 * a + &10 * b + &6 * c = &24
     ==> ?p:int q:num.
           ~(q = 0) /\
           coprime(p,&q) /\
           d = real_of_int p / &q /\
           p + &q = &28`;;
