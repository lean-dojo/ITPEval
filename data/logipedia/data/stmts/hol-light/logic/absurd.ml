(*
  Statement-only formalization of Logipedia corpus artifact logic.absurd,
  catalog title "logic.absurd": a proposition and its negation imply false.
  This file contains no proof.
*)

let logic_absurd =
  `!A:bool. A ==> ~A ==> F`;;
