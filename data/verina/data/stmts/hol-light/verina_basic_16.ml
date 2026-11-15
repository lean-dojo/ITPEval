(*
  Statement-only formalization of VERINA corpus artifact verina_basic_16,
  catalog title "replaceChars": an executable Unicode-string map replaces
  every occurrence of one character with another while preserving length and
  all other characters. This file contains no proof.
*)

let replaceChars_validChar = new_definition
  `replaceChars_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let replaceChars_string = new_definition
  `replaceChars_string (s:num list) <=>
     ALL replaceChars_validChar s`;;

let replaceChars_precond = new_definition
  `replaceChars_precond
      (s:num list) (oldChar:num) (newChar:num) <=> T`;;

let replaceChars = new_definition
  `replaceChars
      (s:num list) (oldChar:num) (newChar:num) =
     MAP
       (\c:num. if c = oldChar then newChar else c)
       s`;;

let replaceChars_postcond = new_definition
  `replaceChars_postcond
      (s:num list) (oldChar:num) (newChar:num)
      (result:num list) <=>
     LENGTH result = LENGTH s /\
     (!i:num.
        i < LENGTH s
        ==> (EL i s = oldChar ==> EL i result = newChar) /\
            (~(EL i s = oldChar) ==> EL i result = EL i s))`;;

let replaceChars_spec_satisfied =
  `!s:num list. !oldChar:num. !newChar:num.
     replaceChars_string s
     ==> replaceChars_validChar oldChar
     ==> replaceChars_validChar newChar
     ==> replaceChars_precond s oldChar newChar
     ==> replaceChars_postcond
           s oldChar newChar
           (replaceChars s oldChar newChar)`;;
