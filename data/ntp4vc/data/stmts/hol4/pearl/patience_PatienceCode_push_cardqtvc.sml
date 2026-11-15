(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/patience_PatienceCode_push_cardqtvc: the patience-solitaire push-card
  verification condition, covering recursive-call preconditions and
  preservation of nonempty stacks. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val patience_wf_stacks_def = Define `
  (patience_wf_stacks ([] : int list list) = T) /\
  (patience_wf_stacks ([] :: rest) = F) /\
  (patience_wf_stacks ((x :: xs) :: rest) =
     patience_wf_stacks rest)`;

val patience_PatienceCode_push_cardqtvc_statement =
  ``!(stacks1 : int list list)
      (acc : int list list)
      (c : int).
      patience_wf_stacks stacks1 /\
      patience_wf_stacks acc
      ==>
      ((case stacks1 of
          [] => T
        | stack :: remaining_stacks =>
            (case stack of
               [] => F
             | top :: tail =>
                 ~(c <= top)
                 ==>
                 (case stacks1 of
                    [] => F
                  | ignored :: f => f = remaining_stacks) /\
                 patience_wf_stacks remaining_stacks /\
                 patience_wf_stacks (stack :: acc))) /\
       (!result : int list list.
          (case stacks1 of
             [] =>
               result =
                 REVERSE ((c :: []) :: acc) ++
                 ([] : int list list)
           | stack :: remaining_stacks =>
               (case stack of
                  [] => F
                | top :: tail =>
                    if c <= top then
                      result =
                        REVERSE ((c :: stack) :: acc) ++
                        remaining_stacks
                    else
                      patience_wf_stacks result))
          ==>
          patience_wf_stacks result))``;
