(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b4
  (putnambench__hol-light__putnam_2020_b4): the average reciprocal weight of
  length-2n integer unit-step paths returning to zero, evaluated at n = 2020.
  This file contains no proof.
*)

let statement =
  `let V =
     \n:num.
       {s:num->int |
          s 0 = &0 /\
          (!j:num. 2 * n <= j ==> s j = &0) /\
          (!j:num.
             1 <= j /\ j <= 2 * n
             ==> abs (s j - s (j - 1)) = &1)} in
   let q =
     \n:num. \s:num->int.
       &1 + sum (1..2 * n - 1) (\j. (&3:real) zpow (s j)) in
   let M =
     \n:num.
       sum (V n) (\v. inv (q n v)) / &(CARD (V n)) in
   M 2020 = &1 / &4040`;;
