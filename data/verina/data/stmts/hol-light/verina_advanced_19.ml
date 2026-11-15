(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_19,
  catalog title "isCleanPalindrome": an executable test filters a string to
  lowercase ASCII letters and checks the resulting character list for being a
  palindrome, together with its total correctness contract. This file contains
  no proof.
*)

let isCleanPalindrome_validChar = new_definition
  `isCleanPalindrome_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let isCleanPalindrome_string = new_definition
  `isCleanPalindrome_string (s:num list) <=>
     ALL isCleanPalindrome_validChar s`;;

let isUpperAlpha = new_definition
  `isUpperAlpha (c:num) <=> 65 <= c /\ c <= 90`;;

let isLowerAlpha = new_definition
  `isLowerAlpha (c:num) <=> 97 <= c /\ c <= 122`;;

let isAlpha = new_definition
  `isAlpha (c:num) <=> isUpperAlpha c \/ isLowerAlpha c`;;

let toLower = new_definition
  `toLower (c:num) =
     if isUpperAlpha c then c + 32 else c`;;

let normalizeChar = new_definition
  `normalizeChar (c:num) =
     if isAlpha c then SOME (toLower c) else NONE`;;

let normalizeString_step =
  new_recursive_definition option_RECURSION
    `(!acc:num list.
        normalizeString_step (NONE:num option) acc = acc) /\
     (!c:num. !acc:num list.
        normalizeString_step (SOME c) acc = CONS c acc)`;;

let normalizeString =
  new_recursive_definition list_RECURSION
    `(normalizeString ([]:num list) = []) /\
     (!c:num. !cs:num list.
        normalizeString (CONS c cs) =
        normalizeString_step
          (normalizeChar c) (normalizeString cs))`;;

let isCleanPalindrome_precond = new_definition
  `isCleanPalindrome_precond (s:num list) <=> T`;;

let reverseList = new_definition
  `reverseList (xs:num list) = REVERSE xs`;;

let isCleanPalindrome = new_definition
  `isCleanPalindrome (s:num list) =
     let norm = normalizeString s in
     norm = reverseList norm`;;

let isCleanPalindrome_postcond = new_definition
  `isCleanPalindrome_postcond (s:num list) (result:bool) <=>
     let norm = normalizeString s in
     (result = T ==> norm = REVERSE norm) /\
     (result = F ==> ~(norm = REVERSE norm))`;;

let isCleanPalindrome_spec_satisfied =
  `!s:num list.
     isCleanPalindrome_string s
     ==> isCleanPalindrome_precond s
     ==> isCleanPalindrome_postcond s (isCleanPalindrome s)`;;
