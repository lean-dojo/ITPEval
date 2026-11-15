(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_f2,
  catalog title "logic.eq_f2": equality of both inputs is preserved by
  applying an arbitrary curried binary function over arbitrary types. This
  file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!f:A->B->C.
   !x1 x2:A.
   !y1 y2:B.
     logipedia_logic_eq x1 x2
     ==> logipedia_logic_eq y1 y2
     ==> logipedia_logic_eq (f x1 y1) (f x2 y2)`;;
