(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reduction2qtvc: the verification
  condition for call-by-value reduction of S-K combinator terms containing
  only K, preserving the term class and reaching a value through the
  reflexive-transitive reduction relation. This file contains no proof.
*)

let ntp4vc_comb_term_INDUCT,ntp4vc_comb_term_RECURSION = define_type
  "ntp4vc_comb_term =
       NTP4VC_COMB_S
     | NTP4VC_COMB_K
     | NTP4VC_COMB_App ntp4vc_comb_term ntp4vc_comb_term";;

let ntp4vc_comb_context_INDUCT,ntp4vc_comb_context_RECURSION = define_type
  "ntp4vc_comb_context =
       NTP4VC_COMB_Hole
     | NTP4VC_COMB_Left ntp4vc_comb_context ntp4vc_comb_term
     | NTP4VC_COMB_Right ntp4vc_comb_term ntp4vc_comb_context";;

let ntp4vc_comb_is_value_RULES,
    ntp4vc_comb_is_value_INDUCT,
    ntp4vc_comb_is_value_CASES =
  new_inductive_definition
   `(ntp4vc_comb_is_value NTP4VC_COMB_K) /\
    (ntp4vc_comb_is_value NTP4VC_COMB_S) /\
    (!v:ntp4vc_comb_term.
       ntp4vc_comb_is_value v
       ==> ntp4vc_comb_is_value (NTP4VC_COMB_App NTP4VC_COMB_K v)) /\
    (!v:ntp4vc_comb_term.
       ntp4vc_comb_is_value v
       ==> ntp4vc_comb_is_value (NTP4VC_COMB_App NTP4VC_COMB_S v)) /\
    (!v1 v2:ntp4vc_comb_term.
       ntp4vc_comb_is_value v1 /\ ntp4vc_comb_is_value v2
       ==> ntp4vc_comb_is_value
             (NTP4VC_COMB_App (NTP4VC_COMB_App NTP4VC_COMB_S v1) v2))`;;

let ntp4vc_comb_is_context =
  new_recursive_definition ntp4vc_comb_context_RECURSION
   `(ntp4vc_comb_is_context NTP4VC_COMB_Hole = T) /\
    (!c:ntp4vc_comb_context.
     !t:ntp4vc_comb_term.
       ntp4vc_comb_is_context (NTP4VC_COMB_Left c t) =
       ntp4vc_comb_is_context c) /\
    (!v:ntp4vc_comb_term.
     !c:ntp4vc_comb_context.
       ntp4vc_comb_is_context (NTP4VC_COMB_Right v c) =
       (ntp4vc_comb_is_value v /\ ntp4vc_comb_is_context c))`;;

let ntp4vc_comb_subst =
  new_recursive_definition ntp4vc_comb_context_RECURSION
   `(!t:ntp4vc_comb_term.
       ntp4vc_comb_subst NTP4VC_COMB_Hole t = t) /\
    (!c:ntp4vc_comb_context.
     !t2 t:ntp4vc_comb_term.
       ntp4vc_comb_subst (NTP4VC_COMB_Left c t2) t =
       NTP4VC_COMB_App (ntp4vc_comb_subst c t) t2) /\
    (!v:ntp4vc_comb_term.
     !c:ntp4vc_comb_context.
     !t:ntp4vc_comb_term.
       ntp4vc_comb_subst (NTP4VC_COMB_Right v c) t =
       NTP4VC_COMB_App v (ntp4vc_comb_subst c t))`;;

let ntp4vc_comb_step_RULES,
    ntp4vc_comb_step_INDUCT,
    ntp4vc_comb_step_CASES =
  new_inductive_definition
   `(!c:ntp4vc_comb_context.
     !v1 v2:ntp4vc_comb_term.
       ntp4vc_comb_is_context c /\
       ntp4vc_comb_is_value v1 /\
       ntp4vc_comb_is_value v2
       ==> ntp4vc_comb_step
             (ntp4vc_comb_subst c
               (NTP4VC_COMB_App
                 (NTP4VC_COMB_App NTP4VC_COMB_K v1) v2))
             (ntp4vc_comb_subst c v1)) /\
    (!c:ntp4vc_comb_context.
     !v1 v2 v3:ntp4vc_comb_term.
       ntp4vc_comb_is_context c /\
       ntp4vc_comb_is_value v1 /\
       ntp4vc_comb_is_value v2 /\
       ntp4vc_comb_is_value v3
       ==> ntp4vc_comb_step
             (ntp4vc_comb_subst c
               (NTP4VC_COMB_App
                 (NTP4VC_COMB_App
                   (NTP4VC_COMB_App NTP4VC_COMB_S v1) v2) v3))
             (ntp4vc_comb_subst c
               (NTP4VC_COMB_App
                 (NTP4VC_COMB_App v1 v3)
                 (NTP4VC_COMB_App v2 v3))))`;;

let ntp4vc_comb_reltr_RULES,
    ntp4vc_comb_reltr_INDUCT,
    ntp4vc_comb_reltr_CASES =
  new_inductive_definition
   `(!x:ntp4vc_comb_term.
       ntp4vc_comb_reltr x x) /\
    (!x y z:ntp4vc_comb_term.
       ntp4vc_comb_reltr x y /\ ntp4vc_comb_step y z
       ==> ntp4vc_comb_reltr x z)`;;

let ntp4vc_comb_subst_c =
  new_recursive_definition ntp4vc_comb_context_RECURSION
   `(!ct:ntp4vc_comb_context.
       ntp4vc_comb_subst_c NTP4VC_COMB_Hole ct = ct) /\
    (!c:ntp4vc_comb_context.
     !t:ntp4vc_comb_term.
     !ct:ntp4vc_comb_context.
       ntp4vc_comb_subst_c (NTP4VC_COMB_Left c t) ct =
       NTP4VC_COMB_Left (ntp4vc_comb_subst_c c ct) t) /\
    (!v:ntp4vc_comb_term.
     !c ct:ntp4vc_comb_context.
       ntp4vc_comb_subst_c (NTP4VC_COMB_Right v c) ct =
       NTP4VC_COMB_Right v (ntp4vc_comb_subst_c c ct))`;;

let ntp4vc_comb_left_context = new_definition
  `ntp4vc_comb_left_context
     (c:ntp4vc_comb_context) (t:ntp4vc_comb_term) =
     ntp4vc_comb_subst_c c (NTP4VC_COMB_Left NTP4VC_COMB_Hole t)`;;

let ntp4vc_comb_right_context = new_definition
  `ntp4vc_comb_right_context
     (c:ntp4vc_comb_context) (v:ntp4vc_comb_term) =
     ntp4vc_comb_subst_c c (NTP4VC_COMB_Right v NTP4VC_COMB_Hole)`;;

let ntp4vc_comb_only_k_RULES,
    ntp4vc_comb_only_k_INDUCT,
    ntp4vc_comb_only_k_CASES =
  new_inductive_definition
   `(ntp4vc_comb_only_k NTP4VC_COMB_K) /\
    (!t1 t2:ntp4vc_comb_term.
       ntp4vc_comb_only_k t1 /\ ntp4vc_comb_only_k t2
       ==> ntp4vc_comb_only_k (NTP4VC_COMB_App t1 t2))`;;

let ntp4vc_comb_k_shape =
  new_recursive_definition ntp4vc_comb_term_RECURSION
   `(ntp4vc_comb_k_shape NTP4VC_COMB_S = F) /\
    (ntp4vc_comb_k_shape NTP4VC_COMB_K = T) /\
    (!f v:ntp4vc_comb_term.
       ntp4vc_comb_k_shape (NTP4VC_COMB_App f v) =
       (f = NTP4VC_COMB_K))`;;

let ntp4vc_comb_apply_result =
  new_recursive_definition ntp4vc_comb_term_RECURSION
   `(!v2 result:ntp4vc_comb_term.
       ntp4vc_comb_apply_result NTP4VC_COMB_S v2 result = F) /\
    (!v2 result:ntp4vc_comb_term.
       ntp4vc_comb_apply_result NTP4VC_COMB_K v2 result =
       (result = NTP4VC_COMB_App NTP4VC_COMB_K v2)) /\
    (!f v3 v2 result:ntp4vc_comb_term.
       ntp4vc_comb_apply_result (NTP4VC_COMB_App f v3) v2 result =
       (f = NTP4VC_COMB_K /\ result = v3))`;;

let ntp4vc_comb_context_extension = new_definition
  `ntp4vc_comb_context_extension
     (c:ntp4vc_comb_context) (ct:ntp4vc_comb_context) <=>
     (ntp4vc_comb_is_context c /\ ntp4vc_comb_is_context ct
      ==> ntp4vc_comb_is_context (ntp4vc_comb_subst_c c ct))`;;

let ntp4vc_comb_component = new_definition
  `ntp4vc_comb_component
     (t:ntp4vc_comb_term) (x:ntp4vc_comb_term) <=>
     ?f f1:ntp4vc_comb_term.
       t = NTP4VC_COMB_App f f1 /\ (f = x \/ f1 = x)`;;

let ntp4vc_comb_evaluation = new_definition
  `ntp4vc_comb_evaluation
     (c:ntp4vc_comb_context)
     (input:ntp4vc_comb_term)
     (value:ntp4vc_comb_term) <=>
     (ntp4vc_comb_only_k value /\ ntp4vc_comb_is_value value) /\
     ntp4vc_comb_reltr
       (ntp4vc_comb_subst c input)
       (ntp4vc_comb_subst c value)`;;

let ntp4vc_comb_reduction2_second_measure = new_definition
  `ntp4vc_comb_reduction2_second_measure
     (t:ntp4vc_comb_term)
     (t2:ntp4vc_comb_term)
     (c:ntp4vc_comb_context)
     (v1:ntp4vc_comb_term) <=>
     (ntp4vc_comb_context_extension
        c (NTP4VC_COMB_Right v1 NTP4VC_COMB_Hole)
      ==>
      (ntp4vc_comb_component t t2 /\
       ntp4vc_comb_only_k t2 /\
       ntp4vc_comb_is_context (ntp4vc_comb_right_context c v1)) /\
      (!v2:ntp4vc_comb_term.
         ntp4vc_comb_evaluation
           (ntp4vc_comb_right_context c v1) t2 v2
         ==> ntp4vc_comb_k_shape v1))`;;

let ntp4vc_comb_reduction2_app_measure = new_definition
  `ntp4vc_comb_reduction2_app_measure
     (t:ntp4vc_comb_term)
     (t1:ntp4vc_comb_term)
     (t2:ntp4vc_comb_term)
     (c:ntp4vc_comb_context) <=>
     (ntp4vc_comb_context_extension
        c (NTP4VC_COMB_Left NTP4VC_COMB_Hole t2)
      ==>
      (ntp4vc_comb_component t t1 /\
       ntp4vc_comb_only_k t1 /\
       ntp4vc_comb_is_context (ntp4vc_comb_left_context c t2)) /\
      (!v1:ntp4vc_comb_term.
         ntp4vc_comb_evaluation
           (ntp4vc_comb_left_context c t2) t1 v1
         ==> ntp4vc_comb_reduction2_second_measure t t2 c v1))`;;

let ntp4vc_comb_reduction2_measure = new_definition
  `ntp4vc_comb_reduction2_measure
     (t:ntp4vc_comb_term) (c:ntp4vc_comb_context) <=>
     t = NTP4VC_COMB_K \/
     ?t1 t2:ntp4vc_comb_term.
       t = NTP4VC_COMB_App t1 t2 /\
       ntp4vc_comb_reduction2_app_measure t t1 t2 c`;;

let ntp4vc_comb_reduction2_result_tail = new_definition
  `ntp4vc_comb_reduction2_result_tail
     (t2:ntp4vc_comb_term)
     (c:ntp4vc_comb_context)
     (v1:ntp4vc_comb_term)
     (result:ntp4vc_comb_term) <=>
     ntp4vc_comb_context_extension
       c (NTP4VC_COMB_Right v1 NTP4VC_COMB_Hole) /\
     ?v2:ntp4vc_comb_term.
       ntp4vc_comb_evaluation
         (ntp4vc_comb_right_context c v1) t2 v2 /\
       ntp4vc_comb_apply_result v1 v2 result`;;

let ntp4vc_comb_reduction2_app_result = new_definition
  `ntp4vc_comb_reduction2_app_result
     (t1:ntp4vc_comb_term)
     (t2:ntp4vc_comb_term)
     (c:ntp4vc_comb_context)
     (result:ntp4vc_comb_term) <=>
     ntp4vc_comb_context_extension
       c (NTP4VC_COMB_Left NTP4VC_COMB_Hole t2) /\
     ?v1:ntp4vc_comb_term.
       ntp4vc_comb_evaluation
         (ntp4vc_comb_left_context c t2) t1 v1 /\
       ntp4vc_comb_reduction2_result_tail t2 c v1 result`;;

let ntp4vc_comb_reduction2_result_case = new_definition
  `ntp4vc_comb_reduction2_result_case
     (t:ntp4vc_comb_term)
     (c:ntp4vc_comb_context)
     (result:ntp4vc_comb_term) <=>
     (t = NTP4VC_COMB_K /\ result = NTP4VC_COMB_K) \/
     ?t1 t2:ntp4vc_comb_term.
       t = NTP4VC_COMB_App t1 t2 /\
       ntp4vc_comb_reduction2_app_result t1 t2 c result`;;

let statement =
  `!t:ntp4vc_comb_term.
   !c:ntp4vc_comb_context.
     ntp4vc_comb_only_k t
     ==>
     ntp4vc_comb_is_context c
     ==>
     ntp4vc_comb_reduction2_measure t c /\
     (!result:ntp4vc_comb_term.
        ntp4vc_comb_reduction2_result_case t c result
        ==>
        (ntp4vc_comb_only_k result /\ ntp4vc_comb_is_value result) /\
        ntp4vc_comb_reltr
          (ntp4vc_comb_subst c t)
          (ntp4vc_comb_subst c result))`;;
