(*
  Statement-only formalization of VERINA corpus artifact verina_basic_67
  (verina__hol-light__verina_basic_67), catalog title "IsPalindrome": an
  executable inward scan decides whether a Unicode character list is a
  palindrome, together with its total precondition and exact Boolean
  correctness contract. This file contains no proof.
*)

let IsPalindrome_validChar = new_definition
  `IsPalindrome_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let IsPalindrome_string = new_definition
  `IsPalindrome_string (x:num list) <=>
     ALL IsPalindrome_validChar x`;;

let IsPalindrome_precond = new_definition
  `IsPalindrome_precond (x:num list) <=> T`;;

let isPalindromeHelper =
  new_recursive_definition num_RECURSION
    `(!x:num list. !i:num.
        isPalindromeHelper x i 0 = T) /\
     (!x:num list. !i:num. !j:num.
        isPalindromeHelper x i (SUC j) =
        if i < SUC j then
          if i < LENGTH x /\ SUC j < LENGTH x then
            if ~(EL i x = EL (SUC j) x) then
              F
            else
              isPalindromeHelper x (i + 1) j
          else
            F
        else
          T)`;;

let IsPalindrome = new_definition
  `IsPalindrome (x:num list) =
     if LENGTH x = 0 then
       T
     else
       isPalindromeHelper x 0 (LENGTH x - 1)`;;

let IsPalindrome_postcond = new_definition
  `IsPalindrome_postcond (x:num list) (result:bool) <=>
     (result <=>
      !i:num.
        i < LENGTH x
        ==> EL i x = EL (LENGTH x - i - 1) x)`;;

let IsPalindrome_spec_satisfied =
  `!x:num list.
     IsPalindrome_string x
     ==> IsPalindrome_precond x
     ==> IsPalindrome_postcond x (IsPalindrome x)`;;
