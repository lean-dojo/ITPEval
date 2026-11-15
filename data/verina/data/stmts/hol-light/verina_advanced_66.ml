(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_66,
  catalog title "reverseWords": an executable string transformation splits on
  space characters, removes empty fields, reverses the words, and rejoins them
  with single spaces, together with its total correctness contract. This file
  contains no proof.
*)

let reverseWords_validChar = new_definition
  `reverseWords_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let reverseWords_string = new_definition
  `reverseWords_string (s:num list) <=>
     ALL reverseWords_validChar s`;;

let reverseWords_precond = new_definition
  `reverseWords_precond (words_str:num list) <=> T`;;

let reverseWords_splitOnSpace =
  new_recursive_definition list_RECURSION
    `(reverseWords_splitOnSpace ([]:num list) =
        CONS ([]:num list) []) /\
     (!c:num. !cs:num list.
        reverseWords_splitOnSpace (CONS c cs) =
        if c = 32 then
          CONS [] (reverseWords_splitOnSpace cs)
        else
          let parts = reverseWords_splitOnSpace cs in
          CONS (CONS c (HD parts)) (TL parts))`;;

let reverseWords_filterNonEmpty =
  new_recursive_definition list_RECURSION
    `(reverseWords_filterNonEmpty ([]:(num list) list) = []) /\
     (!w:num list. !ws:(num list) list.
        reverseWords_filterNonEmpty (CONS w ws) =
        let rest = reverseWords_filterNonEmpty ws in
        if w = [] then rest else CONS w rest)`;;

let reverseWords_joinWithSpace =
  new_recursive_definition list_RECURSION
    `(reverseWords_joinWithSpace ([]:(num list) list) = []) /\
     (!w:num list. !ws:(num list) list.
        reverseWords_joinWithSpace (CONS w ws) =
        if ws = [] then w
        else
          APPEND w
            (CONS 32 (reverseWords_joinWithSpace ws)))`;;

let reverseWords_intercalateSpace =
  new_recursive_definition list_RECURSION
    `(reverseWords_intercalateSpace ([]:(num list) list) = []) /\
     (!w:num list. !ws:(num list) list.
        reverseWords_intercalateSpace (CONS w ws) =
        if ws = [] then w
        else
          APPEND w
            (CONS 32 (reverseWords_intercalateSpace ws)))`;;

let reverseWords = new_definition
  `reverseWords (words_str:num list) =
     let rawWords = reverseWords_splitOnSpace words_str in
     let filteredWords =
       reverseWords_filterNonEmpty rawWords in
     let revWords = REVERSE filteredWords in
     reverseWords_joinWithSpace revWords`;;

let reverseWords_postcond = new_definition
  `reverseWords_postcond
      (words_str:num list) (result:num list) <=>
     ?words:(num list) list.
       words =
         FILTER (\w:num list. ~(w = []))
           (reverseWords_splitOnSpace words_str) /\
       result =
         reverseWords_intercalateSpace (REVERSE words)`;;

let reverseWords_spec_satisfied =
  `!words_str:num list.
     reverseWords_string words_str
     ==> reverseWords_precond words_str
     ==> reverseWords_postcond
           words_str (reverseWords words_str)`;;
