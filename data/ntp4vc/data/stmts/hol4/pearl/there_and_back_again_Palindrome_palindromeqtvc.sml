(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Palindrome_palindromeqtvc: the top-level
  palindrome verification condition over reflected integer indices, normal
  recursive returns, and exceptional mismatch witnesses. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory optionTheory;

val there_and_back_again_Palindrome_palindrome_vc =
  ``let nth_opt =
      \xs : 'a list. \i : int.
        if i < (0 : int) then
          (NONE : 'a option)
        else if Num i < LENGTH xs then
          SOME (EL (Num i) xs)
        else
          NONE
    in
    let pal =
      \xs : 'a list. \n : int.
        !i : int.
          (0 : int) <= i /\ i < n ==>
          nth_opt xs i = nth_opt xs (n - (1 : int) - i)
    in
      !x : 'a list.
        LENGTH x <= LENGTH x /\
        (!o1 : 'a list.
           ((?x0 : 'a list.
               LENGTH x0 = LENGTH x /\
               x = APPEND x0 o1) /\
            pal x (&(LENGTH x))) ==>
           pal x (&(LENGTH x))) /\
        ((?i : int.
            ((0 : int) <= i /\ i < &(LENGTH x)) /\
            ~(nth_opt x i =
              nth_opt x (&(LENGTH x) - (1 : int) - i))) ==>
         ~pal x (&(LENGTH x)))``;
