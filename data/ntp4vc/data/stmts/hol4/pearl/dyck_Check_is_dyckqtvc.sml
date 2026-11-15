(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/dyck_Check_is_dyckqtvc: a Dyck-word recognition verification
  condition relating a unique balanced-prefix decomposition to a Boolean
  result and rejecting words with no such decomposition. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open listTheory;

Datatype:
  dyck_paren = DyckL | DyckR
End

val (dyck_word_rules,
     dyck_word_ind,
     dyck_word_cases) =
  Hol_reln `
    dyck_word ([] : dyck_paren list) /\
    (!w1 w2.
       dyck_word w1 /\
       dyck_word w2 ==>
       dyck_word (DyckL :: (w1 ++ (DyckR :: w2))))
  `;

val dyck_fall_def = Define `
  dyck_fall p s <=>
    dyck_word p /\
    case s of
      [] => T
    | DyckL :: rest => F
    | DyckR :: rest => T`;

val dyck_Check_is_dyck_vc =
  ``!w o2 : dyck_paren list.
      (!o1 : dyck_paren list.
         w = o2 ++ o1 /\
         dyck_fall o2 o1 /\
         (!p2 s : dyck_paren list.
            w = p2 ++ s /\
            dyck_fall p2 s ==>
            p2 = o2 /\
            s = o1) ==>
         !result : bool.
           (case o1 of
              [] => result = T
            | head :: rest => result = F) ==>
           ((result = T) <=> dyck_word w)) /\
      ((!p s : dyck_paren list.
          w = p ++ s ==>
          ~dyck_fall p s) ==>
       ~dyck_word w)``;
