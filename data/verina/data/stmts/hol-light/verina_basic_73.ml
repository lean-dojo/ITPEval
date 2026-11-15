(*
  Statement-only formalization of VERINA corpus artifact verina_basic_73
  (verina__hol-light__verina_basic_73), catalog title "Match": an executable
  equal-length Unicode string scan decides pointwise pattern matching, where
  question mark is the wildcard, together with its exact Boolean correctness
  contract. This file contains no proof.
*)

let match_validChar_def = new_definition
  `Match_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let match_string_def = new_definition
  `Match_string (s:num list) <=>
     ALL Match_validChar s`;;

let match_precond_def = new_definition
  `Match_precond (s:num list) (p:num list) <=>
     LENGTH s = LENGTH p`;;

let match_getDefault_def = new_definition
  `Match_getDefault (xs:num list) (i:num) =
     if i < LENGTH xs then EL i xs else 0`;;

let match_loopFuel_def =
  new_recursive_definition num_RECURSION
    `(!s:num list. !p:num list. !i:num.
        Match_loopFuel 0 s p i = T) /\
     (!fuel:num. !s:num list. !p:num list. !i:num.
        Match_loopFuel (SUC fuel) s p i =
        if i < LENGTH s then
          if ~(Match_getDefault s i =
               Match_getDefault p i) /\
             ~(Match_getDefault p i = 63)
          then F
          else Match_loopFuel fuel s p (i + 1)
        else T)`;;

let match_def = new_definition
  `Match (s:num list) (p:num list) =
     Match_loopFuel (LENGTH s) s p 0`;;

let match_postcond_def = new_definition
  `Match_postcond
      (s:num list) (p:num list) (result:bool) <=>
     ((result = T) <=>
      !n:num.
        n < LENGTH s
        ==> Match_getDefault s n = Match_getDefault p n \/
            Match_getDefault p n = 63)`;;

let match_spec_satisfied =
  `!s:num list. !p:num list.
     Match_string s
     ==> Match_string p
     ==> Match_precond s p
     ==> Match_postcond s p (Match s p)`;;
