(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b1:
  the minimum value of a rational expression in a positive real variable is
  six. This file contains no proof.
*)

let statement =
  `let objective =
     \x:real.
       ((x + &1 / x) pow 6 -
        (x pow 6 + &1 / (x pow 6)) -
        &2) /
       ((x + &1 / x) pow 3 +
        (x pow 3 + &1 / (x pow 3))) in
   (!x:real. &0 < x ==> &6 <= objective x) /\
   (?x:real. &0 < x /\ objective x = &6)`;;
