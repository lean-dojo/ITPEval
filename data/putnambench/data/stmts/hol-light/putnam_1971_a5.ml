(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a5:
  positive integer point values with exactly 35 unattainable natural scores,
  including 58, are characterized by the pair (11,8). This file contains no
  proof.
*)

let statement =
  `let unattainable =
     \(x:int) (y:int).
       {s:num |
          ~(?m n:num.
              (&m:int) * x + (&n:int) * y = (&s:int))} in
   !a b:int.
     (&0:int) < a /\ (&0:int) < b /\ b < a
     ==>
     ((FINITE (unattainable a b) /\
       CARD (unattainable a b) = 35 /\
       58 IN unattainable a b)
      <=>
      a = (&11:int) /\ b = (&8:int))`;;
