(*
  Statement-only formalization of miniF2F valid problem imo_1984_p2. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1984_p2: if positive natural numbers a and b
  have none of a, b, or a + b divisible by 7, while 7^7 divides
  (a + b)^7 - a^7 - b^7, then 19 <= a + b.
  This is a statement-only formalization and contains no proof.
*)

let imo_1984_p2 =
  `!a b:num.
     0 < a /\ 0 < b /\
     ~(7 divides a) /\
     ~(7 divides b) /\
     ~(7 divides (a + b)) /\
     (7 EXP 7) divides ((a + b) EXP 7 - a EXP 7 - b EXP 7)
     ==> 19 <= a + b`;;
