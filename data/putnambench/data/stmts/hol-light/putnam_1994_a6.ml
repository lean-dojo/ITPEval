(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a6:
  at most half of the 0/1 ordered compositions of ten integer permutations
  can preserve any given finite nonempty set of integers. This file contains
  no proof.
*)

needs "Library/iter.ml";;

let statement =
  `!f:num->int->int.
   !mijcomp:num->(num->num)->num->int->int.
   !fam:(int->int)->bool.
     (!i:num. i < 10 ==> BIJ (f i) (:int) (:int)) /\
     (!n:int.
        ?m:num. ?i:num->num.
          1 <= m /\
          (!j:num. j < m ==> i j < 10) /\
          mijcomp m i 0 (&0) = n) /\
     (!m:num. !i:num->num. !j:num.
        1 <= m /\ j < m
        ==> mijcomp m i j =
            if j = m - 1 then
              f (i j)
            else
              f (i j) o mijcomp m i (j + 1)) /\
     fam =
       {g:int->int |
          ?e:num->num.
            (!i:num. i < 10 ==> e i = 0 \/ e i = 1) /\
            g =
              (ITER (e 0) (f 0)) o
              (ITER (e 1) (f 1)) o
              (ITER (e 2) (f 2)) o
              (ITER (e 3) (f 3)) o
              (ITER (e 4) (f 4)) o
              (ITER (e 5) (f 5)) o
              (ITER (e 6) (f 6)) o
              (ITER (e 7) (f 7)) o
              (ITER (e 8) (f 8)) o
              (ITER (e 9) (f 9))}
     ==>
     !A:int->bool.
       FINITE A /\ ~(A = {})
       ==> CARD {g:int->int | g IN fam /\ IMAGE g A = A} <= 512`;;
