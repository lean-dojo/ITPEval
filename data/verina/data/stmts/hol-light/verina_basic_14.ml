(*
  Statement-only formalization of VERINA corpus artifact verina_basic_14,
  catalog title "containsZ": an executable Unicode-string scan returns true
  exactly when the input contains lowercase or uppercase z, together with its
  total precondition and Boolean correctness contract. This file contains no
  proof.
*)

let containsZ_validChar = new_definition
  `containsZ_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let containsZ_string = new_definition
  `containsZ_string (s:num list) <=>
     ALL containsZ_validChar s`;;

let containsZ_precond = new_definition
  `containsZ_precond (s:num list) <=> T`;;

let containsZ =
  new_recursive_definition list_RECURSION
    `(containsZ ([]:num list) = F) /\
     (!c:num. !cs:num list.
        containsZ (CONS c cs) =
        (c = 122 \/ c = 90 \/ containsZ cs))`;;

let containsZ_postcond = new_definition
  `containsZ_postcond (s:num list) (result:bool) <=>
     ((?x:num. MEM x s /\ (x = 122 \/ x = 90)) <=> result)`;;

let containsZ_spec_satisfied =
  `!s:num list.
     containsZ_string s
     ==> containsZ_precond s
     ==> containsZ_postcond s (containsZ s)`;;
