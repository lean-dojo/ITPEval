(*
  Statement-only formalization of VERINA corpus artifact verina_basic_38
  (verina__hol-light__verina_basic_38), catalog title "allCharactersSame": an
  executable Unicode-string check returns true exactly when every character
  is identical, together with its total precondition and full Boolean
  correctness contract. This file contains no proof.
*)

let allCharactersSame_validChar = new_definition
  `allCharactersSame_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let allCharactersSame_string = new_definition
  `allCharactersSame_string (s:num list) <=>
     ALL allCharactersSame_validChar s`;;

let allCharactersSame_precond = new_definition
  `allCharactersSame_precond (s:num list) <=> T`;;

let allCharactersSame =
  new_recursive_definition list_RECURSION
    `(allCharactersSame ([]:num list) = T) /\
     (!c:num. !cs:num list.
        allCharactersSame (CONS c cs) =
        ALL (\x:num. x = c) cs)`;;

let allCharactersSame_pairwise =
  new_recursive_definition list_RECURSION
    `(allCharactersSame_pairwise ([]:num list) <=> T) /\
     (!c:num. !cs:num list.
        allCharactersSame_pairwise (CONS c cs) <=>
        ALL (\x:num. c = x) cs /\
        allCharactersSame_pairwise cs)`;;

let allCharactersSame_postcond = new_definition
  `allCharactersSame_postcond
      (s:num list) (result:bool) <=>
     (result ==> allCharactersSame_pairwise s) /\
     (~result
      ==> ~(s = []) /\
          (?x:num. MEM x s /\ ~(x = HD s)))`;;

let allCharactersSame_spec_satisfied =
  `!s:num list.
     allCharactersSame_string s
     ==> allCharactersSame_precond s
     ==> allCharactersSame_postcond
           s (allCharactersSame s)`;;
