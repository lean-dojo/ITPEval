(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b4:
  an integer polynomial in three variables recovers x from
  x^n, x^(n+1), and x + x^(n+2). This file contains no proof.
*)

let statement =
  `let eval1 =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let eval2 =
     \p:(int list)list. \x:int. \y:int.
       eval1 (MAP (\q:int list. eval1 q y) p) x in
   let eval3 =
     \p:((int list)list)list. \x:int. \y:int. \z:int.
       eval1 (MAP (\q:(int list)list. eval2 q y z) p) x in
   !n:num.
     1 < n
     ==> ?p:((int list)list)list.
           !x:int.
             x =
             eval3 p
               (x pow n)
               (x pow (n + 1))
               (x + x pow (n + 2))`;;
