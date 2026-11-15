(*
  Statement-only formalization of VERINA corpus artifact verina_basic_36
  (verina__hol-light__verina_basic_36), catalog title "replaceWithColon": an
  executable Unicode-string map replaces spaces, commas, and dots with colons
  and leaves all other characters unchanged, together with its total
  length-preserving correctness contract. This file contains no proof.
*)

let replaceWithColon_validChar = new_definition
  `replaceWithColon_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let replaceWithColon_string = new_definition
  `replaceWithColon_string (s:num list) <=>
     ALL replaceWithColon_validChar s`;;

let isSpaceCommaDot = new_definition
  `isSpaceCommaDot (c:num) <=>
     c = 32 \/ c = 44 \/ c = 46`;;

let replaceWithColon_precond = new_definition
  `replaceWithColon_precond (s:num list) <=> T`;;

let replaceWithColon = new_definition
  `replaceWithColon (s:num list) =
     MAP
       (\c:num. if isSpaceCommaDot c then 58 else c)
       s`;;

let replaceWithColon_postcond = new_definition
  `replaceWithColon_postcond
      (s:num list) (result:num list) <=>
     LENGTH result = LENGTH s /\
     (!i:num.
        i < LENGTH s
        ==> (isSpaceCommaDot (EL i s)
             ==> EL i result = 58) /\
            (~isSpaceCommaDot (EL i s)
             ==> EL i result = EL i s))`;;

let replaceWithColon_spec_satisfied =
  `!s:num list.
     replaceWithColon_string s
     ==> replaceWithColon_precond s
     ==> replaceWithColon_postcond
           s (replaceWithColon s)`;;
