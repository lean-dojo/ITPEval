(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/patience_PatienceCode_push_cardqtvc: the verification condition for
  pushing an integer-valued card onto the leftmost eligible nonempty patience
  stack while preserving well-formed stacks. This file contains no proof.
*)

let ntp4vc_patience_push_wf_stacks =
  new_recursive_definition list_RECURSION
   `(ntp4vc_patience_push_wf_stacks ([]:(int list) list) = T) /\
    (!stack:int list. !remaining:(int list) list.
       ntp4vc_patience_push_wf_stacks (CONS stack remaining) =
       (~(stack = []) /\
        ntp4vc_patience_push_wf_stacks remaining))`;;

let statement =
 `!stacks1 acc:(int list) list. !c:int.
    ntp4vc_patience_push_wf_stacks stacks1 ==>
    ntp4vc_patience_push_wf_stacks acc ==>
    ((if stacks1 = [] then
        T
      else
        let stack = HD stacks1 in
        let remaining_stacks = TL stacks1 in
        if stack = [] then
          F
        else
          ~(c <= HD stack)
          ==>
          TL stacks1 = remaining_stacks /\
          ntp4vc_patience_push_wf_stacks remaining_stacks /\
          ntp4vc_patience_push_wf_stacks (CONS stack acc)) /\
     (!result:(int list) list.
        (if stacks1 = [] then
           result =
             APPEND
               (REVERSE (CONS (CONS c []) acc))
               []
         else
           let stack = HD stacks1 in
           let remaining_stacks = TL stacks1 in
           if stack = [] then
             F
           else if c <= HD stack then
             result =
               APPEND
                 (REVERSE (CONS (CONS c stack) acc))
                 remaining_stacks
           else
             ntp4vc_patience_push_wf_stacks result)
        ==>
        ntp4vc_patience_push_wf_stacks result))`;;
