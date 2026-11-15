(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b2:
  every finite nonempty set of n real numbers has a nonempty subset whose sum,
  after adding an integer, has absolute value at most 1 / (n + 1). This file
  contains no proof.
*)

let statement =
  `!n:num. !X:real->bool.
     0 < n /\ FINITE X /\ CARD X = n
     ==> ?S:real->bool.
           S SUBSET X /\
           ~(S = {}) /\
           ?m:int.
             abs (real_of_int m + sum S (\s:real. s)) <=
             &1 / &(n + 1)`;;
