(*
  Statement-only formalization of miniF2F test problem imo_1981_p6. This file contains no proof.
*)

let statement =
  `!f:num->num->num.
    ((!y. f 0 y = y + 1) /\
     (!x. f (x + 1) 0 = f x 1) /\
     (!x y. f (x + 1) (y + 1) = f x (f (x + 1) y)))
    ==> ((!y. f 4 (y + 1) = 2 EXP (f 4 y + 3) - 3) /\
         (!g:num->num.
           (g 0 = 2 /\
            (!n. g (n + 1) = 2 EXP (g n)))
           ==> f 4 1981 = g 1983 - 3))`;;
