(*
  Statement-only formalization of Logipedia corpus artifact bool.bool_discr,
  catalog title "bool.bool_discr": equal Boolean inputs make the nested
  Boolean eliminators over propositions select a tautological branch. This
  file contains no proof.
*)

let statement =
  `!x y:bool.
     x = y
     ==>
     (if x then
        (if y then (!P:bool. P ==> P) else (!P:bool. P))
      else
        (if y then (!P:bool. P) else (!P:bool. P ==> P)))`;;
