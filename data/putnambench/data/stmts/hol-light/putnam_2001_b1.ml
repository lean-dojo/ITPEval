(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b1:
  an even square grid with half of each row and column in each of two colors
  has equal sums of its row-major entries on the two colors. This file
  contains no proof.
*)

let statement =
  `!n:num.
   !nums:num->num->int.
   !colors:num->num->num.
     0 < n /\
     EVEN n /\
     (!k l:num.
        k < n /\ l < n
        ==> nums k l = &(k * n + l + 1)) /\
     (!k l:num.
        k < n /\ l < n
        ==> colors k l < 2) /\
     (!k:num.
        k < n
        ==> nsum (0..n - 1)
              (\l:num. if colors k l = 0 then 1 else 0) =
            n DIV 2) /\
     (!l:num.
        l < n
        ==> nsum (0..n - 1)
              (\k:num. if colors k l = 0 then 1 else 0) =
            n DIV 2)
     ==>
     isum (0..n - 1)
       (\k:num.
          isum (0..n - 1)
            (\l:num.
               if colors k l = 0 then nums k l else (&0:int))) =
     isum (0..n - 1)
       (\k:num.
          isum (0..n - 1)
            (\l:num.
               if colors k l = 1 then nums k l else (&0:int)))`;;
