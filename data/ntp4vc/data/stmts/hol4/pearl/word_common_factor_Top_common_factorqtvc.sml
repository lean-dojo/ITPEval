(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/word_common_factor_Top_common_factorqtvc: the recursive common-word
  factor verification condition for two commuting words, with integer
  exponents and the defining equation for word powers. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val word_common_factor_Top_common_factor_vc =
  ``!(power : 'char list -> int -> 'char list).
      (!n : int.
       !w : 'char list.
         (0 : int) <= n ==>
         (if n = (0 : int) then
            power w n = []
          else
            power w n =
              APPEND w (power w (n - (1 : int))))) ==>
      !a b : 'char list.
        APPEND a b = APPEND b a ==>
        let o1 = &(LENGTH a)
        in
          ((~(o1 = (0 : int)) ==>
            ~(&(LENGTH b) = (0 : int)) ==>
            (if LENGTH a <= LENGTH b then
               let o2 = &(LENGTH a);
                   c = DROP (Num o2) b
               in
                 ((0 : int) <= o2 /\ o2 <= &(LENGTH b)) /\
                 (b = APPEND a c /\
                  (b = APPEND a c ==>
                   (((0 : int) <= &(LENGTH b) /\
                     &(LENGTH c) < &(LENGTH b)) /\
                    APPEND a c = APPEND c a)))
             else
               ((((0 : int) <= &(LENGTH a) /\
                  &(LENGTH b) < &(LENGTH a)) \/
                 (LENGTH a = LENGTH b /\
                  (0 : int) <= &(LENGTH b) /\
                  &(LENGTH a) < &(LENGTH b))) /\
                APPEND b a = APPEND a b))) /\
           (!w : 'char list.
            !ka kb : int.
              (if o1 = (0 : int) then
                 w = b /\ ka = (0 : int) /\ kb = (1 : int)
               else if &(LENGTH b) = (0 : int) then
                 w = a /\ ka = (1 : int) /\ kb = (0 : int)
               else if LENGTH a <= LENGTH b then
                 let c = DROP (LENGTH a) b
                 in
                   b = APPEND a c /\
                   ?kb1 : int.
                     ((((0 : int) <= ka /\ a = power w ka) /\
                       (0 : int) <= kb1 /\ c = power w kb1) /\
                      kb = ka + kb1)
               else
                 ((0 : int) <= kb /\ b = power w kb) /\
                 (0 : int) <= ka /\ a = power w ka) ==>
              (((0 : int) <= ka /\ a = power w ka) /\
               (0 : int) <= kb /\ b = power w kb))``;
