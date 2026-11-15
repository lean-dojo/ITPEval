(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_405. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_405: exactly two positive natural
  numbers satisfy x^2 + 4*x + 4 < 20, namely 1 and 2. This is a
  statement-only formalization and contains no proof.
*)

let statement =
  `!S:num->bool.
     (!x:num. x IN S <=>
              0 < x /\ x EXP 2 + 4 * x + 4 < 20)
     ==> (S HAS_SIZE 2 /\
          (!x:num. x IN S ==> x = 1 \/ x = 2))`;;
