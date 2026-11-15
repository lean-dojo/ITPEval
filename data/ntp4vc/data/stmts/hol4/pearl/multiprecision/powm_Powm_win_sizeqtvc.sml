(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_win_sizeqtvc: the signed 32-bit window-size
  verification condition for a threshold cascade returning a value from zero
  through ten, positive for every positive input. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory integer_wordTheory wordsTheory;

val powm_Powm_win_sizeqtvc_statement =
  ``!eb : word32.
    !o1 : bool.
    !result : word32.
      (w2i eb = w2i (0w : word32) ==> o1 = T) ==>
      (o1 = T ==> eb = (0w : word32)) ==>
      (if o1 = T then
         result = (0w : word32)
       else if w2i eb <= (7 : int) then
         result = (1w : word32)
       else if w2i eb <= (25 : int) then
         result = (2w : word32)
       else if w2i eb <= (81 : int) then
         result = (3w : word32)
       else if w2i eb <= (214 : int) then
         result = (4w : word32)
       else if w2i eb <= (673 : int) then
         result = (5w : word32)
       else if w2i eb <= (1793 : int) then
         result = (6w : word32)
       else if w2i eb <= (4609 : int) then
         result = (7w : word32)
       else if w2i eb <= (11521 : int) then
         result = (8w : word32)
       else if w2i eb <= (28161 : int) then
         result = (9w : word32)
       else
         result = (10w : word32)) ==>
      (0 : int) <= w2i result /\
      w2i result <= (10 : int) /\
      ((0 : int) < w2i eb ==> (0 : int) < w2i result)``;
