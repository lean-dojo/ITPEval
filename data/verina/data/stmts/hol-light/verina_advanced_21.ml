(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_21,
  catalog title "isPalindrome": an executable string test conjoins an
  inward index comparison with equality to an accumulator-built reversal,
  together with its total correctness contract. This file contains no proof.
*)

let isPalindrome_validChar = new_definition
  `isPalindrome_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let isPalindrome_string = new_definition
  `isPalindrome_string (s:num list) <=>
     ALL isPalindrome_validChar s`;;

let isPalindrome_precond = new_definition
  `isPalindrome_precond (s:num list) <=> T`;;

let isPalindrome_checkIndices = define
  `isPalindrome_checkIndices(left,right,(chars:num list)) =
     if right <= left then T
     else if left < LENGTH chars /\ right < LENGTH chars then
       if EL left chars = EL right chars then
         isPalindrome_checkIndices(left + 1,right - 1,chars)
       else F
     else F`;;

let isPalindrome_reverseList =
  new_recursive_definition list_RECURSION
    `(!acc:num list.
        isPalindrome_reverseList acc [] = acc) /\
     (!h:num. !t:num list. !acc:num list.
        isPalindrome_reverseList acc (CONS h t) =
        isPalindrome_reverseList (CONS h acc) t)`;;

let isPalindrome = new_definition
  `isPalindrome (s:num list) =
     let length = LENGTH s in
     if length <= 1 then T
     else
       let approach1 =
         isPalindrome_checkIndices(0,length - 1,s) in
       let reversed =
         isPalindrome_reverseList [] s in
       let approach2 = (s = reversed) in
       approach1 /\ approach2`;;

let isPalindrome_postcond = new_definition
  `isPalindrome_postcond (s:num list) (result:bool) <=>
     (result ==> s = REVERSE s) /\
     (~result ==> ~(s = []) /\ ~(s = REVERSE s))`;;

let isPalindrome_spec_satisfied =
  `!s:num list.
     isPalindrome_string s
     ==> isPalindrome_precond s
     ==> isPalindrome_postcond s (isPalindrome s)`;;
