(*
  Statement-only formalization of PutnamBench artifact putnam_1981_a1:
  the limiting normalized greatest exponent of 5 dividing the weighted
  factorial product 1^1 * 2^2 * ... * n^n. This file contains no proof.
*)

let statement =
  `let seq_tends =
     \(u:num->real) l.
       !e. &0 < e
           ==> ?N. !n. N <= n ==> abs (u n - l) < e in
   let P =
     \n k:num.
       5 EXP k divides nproduct (1..n) (\m:num. m EXP m) in
   !E:num->num.
     (!n:num.
        1 <= n
        ==> P n (E n) /\
            (!k:num. P n k ==> k <= E n))
     ==> seq_tends (\n:num. &(E n) / (&n pow 2)) (&1 / &8)`;;
