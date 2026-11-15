(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_59,
  catalog title "palindromeIgnoreNonAlnum": an executable Unicode-string
  computation filters to ASCII letters and digits, lowercases ASCII letters,
  and checks for a palindrome by inward option-index comparison, together with
  its total correctness contract. This file contains no proof.
*)

let palindromeIgnoreNonAlnum_validChar = new_definition
  `palindromeIgnoreNonAlnum_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let palindromeIgnoreNonAlnum_string = new_definition
  `palindromeIgnoreNonAlnum_string (s:num list) <=>
     ALL palindromeIgnoreNonAlnum_validChar s`;;

let palindromeIgnoreNonAlnum_isUpper = new_definition
  `palindromeIgnoreNonAlnum_isUpper (c:num) <=>
     65 <= c /\ c <= 90`;;

let palindromeIgnoreNonAlnum_isLower = new_definition
  `palindromeIgnoreNonAlnum_isLower (c:num) <=>
     97 <= c /\ c <= 122`;;

let palindromeIgnoreNonAlnum_isAlpha = new_definition
  `palindromeIgnoreNonAlnum_isAlpha (c:num) <=>
     palindromeIgnoreNonAlnum_isUpper c \/
     palindromeIgnoreNonAlnum_isLower c`;;

let palindromeIgnoreNonAlnum_isDigit = new_definition
  `palindromeIgnoreNonAlnum_isDigit (c:num) <=>
     48 <= c /\ c <= 57`;;

let palindromeIgnoreNonAlnum_toLower = new_definition
  `palindromeIgnoreNonAlnum_toLower (c:num) =
     if palindromeIgnoreNonAlnum_isUpper c then c + 32 else c`;;

let palindromeIgnoreNonAlnum_cleaned = new_definition
  `palindromeIgnoreNonAlnum_cleaned (s:num list) =
     MAP palindromeIgnoreNonAlnum_toLower
       (FILTER
         (\c:num.
            palindromeIgnoreNonAlnum_isAlpha c \/
            palindromeIgnoreNonAlnum_isDigit c)
         s)`;;

let palindromeIgnoreNonAlnum_getOpt = new_definition
  `palindromeIgnoreNonAlnum_getOpt
      (xs:num list) (index:num) =
     if index < LENGTH xs then SOME (EL index xs)
     else (NONE:num option)`;;

let palindromeIgnoreNonAlnum_check = define
  `palindromeIgnoreNonAlnum_check
      (left,right,(cleaned:num list)) =
     if right <= left then T
     else if
       palindromeIgnoreNonAlnum_getOpt cleaned left =
       palindromeIgnoreNonAlnum_getOpt cleaned right
     then
       palindromeIgnoreNonAlnum_check
         (left + 1,right - 1,cleaned)
     else F`;;

let palindromeIgnoreNonAlnum_precond = new_definition
  `palindromeIgnoreNonAlnum_precond (s:num list) <=> T`;;

let palindromeIgnoreNonAlnum = new_definition
  `palindromeIgnoreNonAlnum (s:num list) =
     let cleaned = palindromeIgnoreNonAlnum_cleaned s in
     let n = LENGTH cleaned in
     let startIndex = 0 in
     let endIndex = if n = 0 then 0 else n - 1 in
     palindromeIgnoreNonAlnum_check
       (startIndex,endIndex,cleaned)`;;

let palindromeIgnoreNonAlnum_postcond = new_definition
  `palindromeIgnoreNonAlnum_postcond
      (s:num list) (result:bool) <=>
     let cleaned = palindromeIgnoreNonAlnum_cleaned s in
     let forward = cleaned in
     let backward = REVERSE cleaned in
     if result then forward = backward
     else ~(forward = backward)`;;

let palindromeIgnoreNonAlnum_spec_satisfied =
  `!s:num list.
     palindromeIgnoreNonAlnum_string s
     ==> palindromeIgnoreNonAlnum_precond s
     ==> palindromeIgnoreNonAlnum_postcond
           s (palindromeIgnoreNonAlnum s)`;;
