(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_26,
  catalog title "letterCombinations": an executable recursive phone-keypad
  expansion maps a Unicode string of digits to all corresponding letter
  combinations, with its total precondition and extensional list
  postcondition. This file contains no proof.
*)

let letterCombinations_validChar = new_definition
  `letterCombinations_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let letterCombinations_string = new_definition
  `letterCombinations_string (s:num list) <=>
     ALL letterCombinations_validChar s`;;

let digitToLetters = new_definition
  `digitToLetters (c:num) =
     if c = 50 then CONS 97 (CONS 98 (CONS 99 []))
     else if c = 51 then CONS 100 (CONS 101 (CONS 102 []))
     else if c = 52 then CONS 103 (CONS 104 (CONS 105 []))
     else if c = 53 then CONS 106 (CONS 107 (CONS 108 []))
     else if c = 54 then CONS 109 (CONS 110 (CONS 111 []))
     else if c = 55 then
       CONS 112 (CONS 113 (CONS 114 (CONS 115 [])))
     else if c = 56 then CONS 116 (CONS 117 (CONS 118 []))
     else if c = 57 then
       CONS 119 (CONS 120 (CONS 121 (CONS 122 [])))
     else []`;;

let letterCombinations_precond = new_definition
  `letterCombinations_precond (digits:num list) <=> T`;;

let letterCombinations_anyEmptyMapping =
  new_recursive_definition list_RECURSION
    `(letterCombinations_anyEmptyMapping ([]:num list) = F) /\
     (!c:num. !cs:num list.
        letterCombinations_anyEmptyMapping (CONS c cs) =
        if digitToLetters c = []
        then T
        else letterCombinations_anyEmptyMapping cs)`;;

let letterCombinations_flatMapPrefix =
  new_recursive_definition list_RECURSION
    `(!rest:(num list)list.
        letterCombinations_flatMapPrefix ([]:num list) rest = []) /\
     (!c:num. !cs:num list. !rest:(num list)list.
        letterCombinations_flatMapPrefix (CONS c cs) rest =
        APPEND
          (MAP (\s:num list. CONS c s) rest)
          (letterCombinations_flatMapPrefix cs rest))`;;

let letterCombinations_go =
  new_recursive_definition list_RECURSION
    `(letterCombinations_go ([]:num list) = []) /\
     (!d:num. !ds:num list.
        letterCombinations_go (CONS d ds) =
        let restCombinations = letterCombinations_go ds in
        let currentLetters = digitToLetters d in
        if restCombinations = []
        then MAP (\c:num. CONS c []) currentLetters
        else
          letterCombinations_flatMapPrefix
            currentLetters restCombinations)`;;

let letterCombinations = new_definition
  `letterCombinations (digits:num list) =
     if letterCombinations_anyEmptyMapping digits
     then []
     else letterCombinations_go digits`;;

let letterCombinations_validDigit = new_definition
  `letterCombinations_validDigit (c:num) <=>
     MEM c
       (CONS 50
         (CONS 51
           (CONS 52
             (CONS 53
               (CONS 54
                 (CONS 55
                   (CONS 56 (CONS 57 []))))))))`;;

let letterCombinations_anyInvalidDigit =
  new_recursive_definition list_RECURSION
    `(letterCombinations_anyInvalidDigit ([]:num list) = F) /\
     (!c:num. !cs:num list.
        letterCombinations_anyInvalidDigit (CONS c cs) =
        if ~letterCombinations_validDigit c
        then T
        else letterCombinations_anyInvalidDigit cs)`;;

let letterCombinations_expectedStep =
  new_recursive_definition list_RECURSION
    `(!letters:num list.
        letterCombinations_expectedStep
          ([]:(num list)list) letters = []) /\
     (!s:num list. !ss:(num list)list. !letters:num list.
        letterCombinations_expectedStep (CONS s ss) letters =
        APPEND
          (MAP
            (\c:num. APPEND s (CONS c []))
            letters)
          (letterCombinations_expectedStep ss letters))`;;

let letterCombinations_expectedFold =
  new_recursive_definition list_RECURSION
    `(!acc:(num list)list.
        letterCombinations_expectedFold
          acc ([]:(num list)list) = acc) /\
     (!letters:num list. !letterLists:(num list)list.
      !acc:(num list)list.
        letterCombinations_expectedFold
          acc (CONS letters letterLists) =
        letterCombinations_expectedFold
          (letterCombinations_expectedStep acc letters)
          letterLists)`;;

let letterCombinations_expected = new_definition
  `letterCombinations_expected (digits:num list) =
     letterCombinations_expectedFold
       (CONS ([]:num list) [])
       (MAP digitToLetters digits)`;;

let letterCombinations_postcond = new_definition
  `letterCombinations_postcond
      (digits:num list) (result:(num list)list) <=>
     if digits = [] then
       result = []
     else if letterCombinations_anyInvalidDigit digits then
       result = []
     else
       let expected = letterCombinations_expected digits in
       LENGTH result = LENGTH expected /\
       ALL (\s:num list. MEM s expected) result /\
       ALL (\s:num list. MEM s result) expected`;;

let letterCombinations_spec_satisfied =
  `!digits:num list.
     letterCombinations_string digits
     ==> letterCombinations_precond digits
     ==> letterCombinations_postcond
           digits (letterCombinations digits)`;;
