(*
  Statement-only formalization of VERINA corpus artifact verina_basic_27,
  catalog title "findFirstRepeatedChar": an executable Unicode-string scan
  returns the character whose second occurrence is earliest, or no character
  when all characters are distinct, together with its total correctness
  contract. This file contains no proof.
*)

let findFirstRepeatedChar_validChar = new_definition
  `findFirstRepeatedChar_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let findFirstRepeatedChar_string = new_definition
  `findFirstRepeatedChar_string (s:num list) <=>
     ALL findFirstRepeatedChar_validChar s`;;

let findFirstRepeatedChar_precond = new_definition
  `findFirstRepeatedChar_precond (s:num list) <=> T`;;

let findFirstRepeatedChar_loop =
  new_recursive_definition list_RECURSION
    `(!seen:num list.
        findFirstRepeatedChar_loop
          ([]:num list) seen = (NONE:num option)) /\
     (!c:num. !cs:num list. !seen:num list.
        findFirstRepeatedChar_loop
          (CONS c cs) seen =
        if MEM c seen then
          SOME c
        else
          findFirstRepeatedChar_loop cs (CONS c seen))`;;

let findFirstRepeatedChar = new_definition
  `findFirstRepeatedChar (s:num list) =
     findFirstRepeatedChar_loop s []`;;

let findFirstRepeatedChar_count =
  new_recursive_definition list_RECURSION
    `(!target:num.
        findFirstRepeatedChar_count
          ([]:num list) target = 0) /\
     (!c:num. !cs:num list. !target:num.
        findFirstRepeatedChar_count
          (CONS c cs) target =
        if c = target then
          SUC (findFirstRepeatedChar_count cs target)
        else
          findFirstRepeatedChar_count cs target)`;;

let findFirstRepeatedChar_idxOf =
  new_recursive_definition list_RECURSION
    `(!target:num.
        findFirstRepeatedChar_idxOf
          ([]:num list) target = 0) /\
     (!c:num. !cs:num list. !target:num.
        findFirstRepeatedChar_idxOf
          (CONS c cs) target =
        if c = target then
          0
        else
          SUC (findFirstRepeatedChar_idxOf cs target))`;;

let findFirstRepeatedChar_secondIndexFrom =
  new_recursive_definition list_RECURSION
    `(!target:num. !firstIndex:num. !currentIndex:num.
        findFirstRepeatedChar_secondIndexFrom
          ([]:num list) target firstIndex currentIndex =
        currentIndex) /\
     (!c:num. !cs:num list. !target:num.
      !firstIndex:num. !currentIndex:num.
        findFirstRepeatedChar_secondIndexFrom
          (CONS c cs) target firstIndex currentIndex =
        if c = target /\ ~(currentIndex = firstIndex) then
          currentIndex
        else
          findFirstRepeatedChar_secondIndexFrom
            cs target firstIndex (SUC currentIndex))`;;

let findFirstRepeatedChar_secondIndex = new_definition
  `findFirstRepeatedChar_secondIndex
      (s:num list) (target:num) =
     findFirstRepeatedChar_secondIndexFrom
       s target (findFirstRepeatedChar_idxOf s target) 0`;;

let findFirstRepeatedChar_take =
  new_recursive_definition num_RECURSION
    `(!s:num list.
        findFirstRepeatedChar_take 0 s = []) /\
     (!n:num. !s:num list.
        findFirstRepeatedChar_take (SUC n) s =
        if s = [] then
          []
        else
          CONS (HD s)
            (findFirstRepeatedChar_take n (TL s)))`;;

let findFirstRepeatedChar_pairwiseDistinct =
  new_recursive_definition list_RECURSION
    `(findFirstRepeatedChar_pairwiseDistinct
        ([]:num list) <=> T) /\
     (!c:num. !cs:num list.
        findFirstRepeatedChar_pairwiseDistinct
          (CONS c cs) <=>
        ALL (\later:num. ~(c = later)) cs /\
        findFirstRepeatedChar_pairwiseDistinct cs)`;;

let findFirstRepeatedChar_postcond_by_result =
  new_recursive_definition option_RECURSION
    `(!s:num list.
        findFirstRepeatedChar_postcond_by_result
          (NONE:num option) s <=>
        findFirstRepeatedChar_pairwiseDistinct s) /\
     (!c:num. !s:num list.
        findFirstRepeatedChar_postcond_by_result
          (SOME c) s <=>
        findFirstRepeatedChar_count s c >= 2 /\
        findFirstRepeatedChar_pairwiseDistinct
          (findFirstRepeatedChar_take
            (findFirstRepeatedChar_secondIndex s c)
            s))`;;

let findFirstRepeatedChar_postcond = new_definition
  `findFirstRepeatedChar_postcond
      (s:num list) (result:num option) <=>
     findFirstRepeatedChar_postcond_by_result result s`;;

let findFirstRepeatedChar_spec_satisfied =
  `!s:num list.
     findFirstRepeatedChar_string s
     ==> findFirstRepeatedChar_precond s
     ==> findFirstRepeatedChar_postcond
           s (findFirstRepeatedChar s)`;;
