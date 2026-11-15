(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b6:
  the greatest odd divisor function on positive integers and a strict bound
  for its normalized partial sums. This file contains no proof.
*)

let statement =
  `let delta =
     \n:num.
       @d:num.
         d divides n /\
         ODD d /\
         (!t:num. t divides n /\ ODD t ==> t <= d) in
   !x:num.
     0 < x
     ==> abs
           (sum (1..x) (\i:num. &(delta i) / &i) -
            &2 * &x / &3)
         < &1`;;
