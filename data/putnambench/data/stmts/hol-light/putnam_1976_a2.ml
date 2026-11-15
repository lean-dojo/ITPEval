(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a2:
  for every positive exponent, one of two symmetric integer bivariate
  polynomials is an integer polynomial in x^2*y + x*y^2 and
  x^2 + x*y + y^2. This file contains no proof.
*)

let statement =
  `let eval1 =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let eval2 =
     \p:(int list)list. \x:int. \y:int.
       eval1 (MAP (\q:int list. eval1 q y) p) x in
   let pform =
     \x:int. \y:int. x pow 2 * y + x * y pow 2 in
   let qform =
     \x:int. \y:int. x pow 2 + x * y + y pow 2 in
   let f =
     \n:num. \x:int. \y:int.
       (x + y) pow n - x pow n - y pow n in
   let g =
     \n:num. \x:int. \y:int.
       (x + y) pow n + x pow n + y pow n in
   !n:num.
     0 < n
     ==> ?a:(int list)list.
           (!x y:int.
              f n x y = eval2 a (pform x y) (qform x y)) \/
           (!x y:int.
              g n x y = eval2 a (pform x y) (qform x y))`;;
