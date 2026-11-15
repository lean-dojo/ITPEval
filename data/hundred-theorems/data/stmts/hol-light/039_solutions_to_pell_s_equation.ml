(*
  Statement-only formalization of "Solutions to Pell's Equation" from Hundred Theorems item 039.
  This file contains no proof.
*)

let SOLUTIONS_TO_PELLS_EQUATION =
  `!D:num.
     ~(?k:num. D = k EXP 2)
     ==> ?x0 y0 (p:num->num#num).
           0 < y0 /\
           x0 EXP 2 = 1 + D * y0 EXP 2 /\
           p 0 = (1,0) /\
           (!n:num.
              p (SUC n) =
              (FST (p n) * x0 + D * SND (p n) * y0,
               FST (p n) * y0 + SND (p n) * x0)) /\
           (!x y:int.
              x pow 2 - &D * y pow 2 = &1 <=>
              ?n:num.
                (x = &(FST (p n)) \/ x = --(&(FST (p n)))) /\
                (y = &(SND (p n)) \/ y = --(&(SND (p n)))))`;;
