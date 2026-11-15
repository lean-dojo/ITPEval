(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b3:
  a sufficiently large set of 2 by 2 natural-number matrices with bounded
  square entries contains two distinct commuting matrices. This file contains
  no proof.
*)

let statement =
  `!S:(num#num#num#num)->bool.
     (!a b c d:num.
        (a,b,c,d) IN S
        ==> (?x:num. a = x EXP 2) /\ a <= 200 /\
            (?x:num. b = x EXP 2) /\ b <= 200 /\
            (?x:num. c = x EXP 2) /\ c <= 200 /\
            (?x:num. d = x EXP 2) /\ d <= 200)
     ==>
     (CARD S > 50387
      ==> ?a b c d e f g h:num.
            (a,b,c,d) IN S /\
            (e,f,g,h) IN S /\
            ~((a,b,c,d) = (e,f,g,h)) /\
            (a * e + b * g, a * f + b * h,
             c * e + d * g, c * f + d * h) =
            (e * a + f * c, e * b + f * d,
             g * a + h * c, g * b + h * d))`;;
