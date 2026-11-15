(*
  Statement-only formalization of miniF2F valid problem aimeII_2020_p6. This file contains no
  proof.
*)

let aimeII_2020_p6 =
  `let is_rat = \x:real.
     ?p:int q:num. ~(q = 0) /\ x = real_of_int p / &q in
   !t:num->real.
     (!n. is_rat (t n)) /\
     t 1 = &20 /\
     t 2 = &21 /\
     (!n. 3 <= n
          ==> t n =
              (&5 * t (n - 1) + &1) /
              (&25 * t (n - 2)))
     ==> ?p:int q:num.
           0 < q /\
           coprime(p,&q) /\
           t 2020 = real_of_int p / &q /\
           p + &q = &626`;;
