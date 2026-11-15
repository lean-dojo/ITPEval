(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b3:
  the least positive uniform upper bound for minima of |c - d * sqrt 3|
  over nonnegative integer pairs with a fixed positive sum.
  This file contains no proof.
*)

let statement =
  `let solution = (&1 + sqrt (&3)) / &2 in
   !r:int->real.
     (!n:int.
        (&1:int) <= n
        ==>
        ((?c d:int.
            (&0:int) <= c /\
            (&0:int) <= d /\
            c + d = n /\
            r n =
            abs (real_of_int c - real_of_int d * sqrt (&3))) /\
         (!c d:int.
            (&0:int) <= c /\
            (&0:int) <= d /\
            c + d = n
            ==> r n <=
                abs (real_of_int c - real_of_int d * sqrt (&3)))))
     ==>
     &0 < solution /\
     (!n:int. (&1:int) <= n ==> r n <= solution) /\
     (!g:real.
        &0 < g /\
        (!n:int. (&1:int) <= n ==> r n <= g)
        ==> solution <= g)`;;
