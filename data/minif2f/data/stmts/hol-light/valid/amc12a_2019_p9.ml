(*
  Statement-only formalization of miniF2F valid problem amc12a_2019_p9. This file contains no
  proof.
*)

(*
  miniF2F valid artifact amc12a_2019_p9: a rational sequence with a 1 = 1,
  a 2 = 3/7, and the stated recurrence has reduced numerator plus denominator
  8078 at index 2019. This is a statement-only formalization and contains no
  proof.
*)

let amc12a_2019_p9 =
  `let is_rat = \x:real.
     ?p:int q:num. ~(q = 0) /\ x = real_of_int p / &q in
   !a:num->real.
     (!n:num. is_rat (a n)) /\
     a 1 = &1 /\
     a 2 = &3 / &7 /\
     (!n:num.
        a (n + 2) =
        (a n * a (n + 1)) /
        (&2 * a n - a (n + 1)))
     ==> ?p:int q:num.
           0 < q /\
           coprime(p,&q) /\
           a 2019 = real_of_int p / &q /\
           p + &q = &8078`;;
