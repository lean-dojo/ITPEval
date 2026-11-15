(*
  Statement-only formalization of Logipedia corpus artifact
  bool.true_or_false, catalog title "bool.true_or_false": every Boolean is
  equal to true or equal to false. This file contains no proof.
*)

let statement =
  `!b:bool. b = T \/ b = F`;;
