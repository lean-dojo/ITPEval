(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a3:
  a sequence initialized by its indices and satisfying a delayed additive
  recurrence has 2005 consecutive terms divisible by 2006. This file contains
  no proof.
*)

let statement =
  `!x:int->int.
     (!k:int.
        &1 <= k /\ k <= &2006
        ==> x k = k) /\
     (!k:int.
        &2006 <= k
        ==> x (k + &1) = x k + x (k - &2005))
     ==>
     ?i:num.
       0 < i /\
       !j:num.
         j < 2005
         ==> (&2006:int) divides x (&i + &j)`;;
