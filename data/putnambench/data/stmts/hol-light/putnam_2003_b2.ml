(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b2:
  repeated adjacent averaging of the rational sequence 1, 1/2, ..., 1/n
  produces a final value strictly less than 2/n. This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   !n:num. !seq:num->num->real.
     0 < n /\
     (!k j:num. is_rational (seq k j)) /\
     (!j:num.
        1 <= j /\ j <= n
        ==> seq 0 j = &1 / &j) /\
     (!k:num.
        1 <= k /\ k <= n - 1
        ==>
        !j:num.
          1 <= j /\ j <= n - k
          ==>
          seq k j =
          (seq (k - 1) j + seq (k - 1) (j + 1)) / &2)
     ==>
     seq (n - 1) 1 < &2 / &n`;;
