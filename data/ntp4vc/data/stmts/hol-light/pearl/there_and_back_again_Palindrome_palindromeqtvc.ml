(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Palindrome_palindromeqtvc: the top-level
  palindrome verification condition, preserving the palindrome predicate on
  normal return and deriving its negation from an in-range mirrored mismatch.
  This file contains no proof.
*)

let statement =
 `let nth_opt =
    \(xs:A list) (i:int).
      if i < (&0:int) then (NONE:A option)
      else if num_of_int i < LENGTH xs then
        SOME (EL (num_of_int i) xs)
      else
        NONE in
  let pal =
    \(xs:A list) (n:int).
      !i:int.
        (&0:int) <= i /\ i < n
        ==> nth_opt xs i = nth_opt xs (n - (&1:int) - i) in
  !x:A list.
    (&(LENGTH x):int) <= (&(LENGTH x):int) /\
    (!o1:A list.
       ((?x0:A list.
           LENGTH x0 = LENGTH x /\
           x = APPEND x0 o1) /\
        pal x (&(LENGTH x):int))
       ==> pal x (&(LENGTH x):int)) /\
    ((?i:int.
        ((&0:int) <= i /\ i < (&(LENGTH x):int)) /\
        ~(nth_opt x i =
          nth_opt x ((&(LENGTH x):int) - (&1:int) - i)))
     ==> ~pal x (&(LENGTH x):int))`;;
