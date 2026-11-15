(*
  Statement-only formalization of miniF2F test problem aime_1990_p15. This file contains no
  proof.
*)

let statement =
  `!a b x y:real.
     (a * x + b * y = &3) /\
     (a * x pow 2 + b * y pow 2 = &7) /\
     (a * x pow 3 + b * y pow 3 = &16) /\
     (a * x pow 4 + b * y pow 4 = &42)
     ==> a * x pow 5 + b * y pow 5 = &20`;;
