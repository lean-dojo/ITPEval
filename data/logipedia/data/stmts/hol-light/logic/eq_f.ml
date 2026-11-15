(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_f,
  catalog title "logic.eq_f": equality of inputs is preserved by applying
  an arbitrary function between arbitrary types. This file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!f:A->B.
   !x y:A.
     logipedia_logic_eq x y
     ==> logipedia_logic_eq (f x) (f y)`;;
