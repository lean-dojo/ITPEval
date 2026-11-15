(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b3:
  the Lebesgue area of the real parameter pairs for which a recursively
  defined sequence converges is 4 + pi. This file contains no proof.
*)

let statement =
  `let cover_bound =
     \(s:(real#real)->bool) (B:real).
       &0 <= B /\
       ?xl xu yl yu:num->real.
         (!k:num. xl k <= xu k /\ yl k <= yu k) /\
         (!p:real#real.
            p IN s
            ==> ?k:num.
                  xl k < FST p /\ FST p < xu k /\
                  yl k < SND p /\ SND p < yu k) /\
         (!N:num.
            sum (0..N)
              (\k:num. (xu k - xl k) * (yu k - yl k)) <= B) in
   let outer_measure =
     \(s:(real#real)->bool).
       inf {B:real | cover_bound s B} in
   let pi =
     outer_measure
       {p:real#real |
          (FST p) pow 2 + (SND p) pow 2 < &1} in
   let putnam_1992_b3_solution = &4 + pi in
   !a:(real#real)->num->real.
     (!p:real#real.
        a p 0 = FST p /\
        (!n:num.
           a p (n + 1) =
           ((a p n) pow 2 + (SND p) pow 2) / &2))
     ==> outer_measure
           {p:real#real |
              ?L:real.
                !e:real.
                  &0 < e
                  ==> ?N:num.
                        !n:num.
                          N <= n ==> abs (a p n - L) < e} =
         putnam_1992_b3_solution`;;
