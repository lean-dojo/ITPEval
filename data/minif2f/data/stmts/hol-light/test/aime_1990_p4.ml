(*
  Statement-only formalization of miniF2F test problem aime_1990_p4. This file contains no
  proof.
*)

let statement = `!x:real.
    &0 < x /\
    ~(x pow 2 - &10 * x - &29 = &0) /\
    ~(x pow 2 - &10 * x - &45 = &0) /\
    ~(x pow 2 - &10 * x - &69 = &0) /\
    (&1 / (x pow 2 - &10 * x - &29) +
     &1 / (x pow 2 - &10 * x - &45) -
     &2 / (x pow 2 - &10 * x - &69) = &0)
    ==> x = &13`;;
