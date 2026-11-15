(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reduction3qtvc: the recursive
  verification condition for call-by-value reduction of iterated K-combinator
  applications, including the parity characterization of the resulting value.
  This file contains no proof.
*)

let ntp4vc_comb3_term_INDUCT,ntp4vc_comb3_term_RECURSION = define_type
  "ntp4vc_comb3_term =
       NTP4VC_COMB3_S
     | NTP4VC_COMB3_K
     | NTP4VC_COMB3_App ntp4vc_comb3_term ntp4vc_comb3_term";;

let ntp4vc_comb3_context_INDUCT,ntp4vc_comb3_context_RECURSION = define_type
  "ntp4vc_comb3_context =
       NTP4VC_COMB3_Hole
     | NTP4VC_COMB3_Left ntp4vc_comb3_context ntp4vc_comb3_term
     | NTP4VC_COMB3_Right ntp4vc_comb3_term ntp4vc_comb3_context";;

let ntp4vc_comb3_is_value_RULES,
    ntp4vc_comb3_is_value_INDUCT,
    ntp4vc_comb3_is_value_CASES =
  new_inductive_definition
   `(ntp4vc_comb3_is_value NTP4VC_COMB3_K) /\
    (ntp4vc_comb3_is_value NTP4VC_COMB3_S) /\
    (!v:ntp4vc_comb3_term.
       ntp4vc_comb3_is_value v
       ==> ntp4vc_comb3_is_value (NTP4VC_COMB3_App NTP4VC_COMB3_K v)) /\
    (!v:ntp4vc_comb3_term.
       ntp4vc_comb3_is_value v
       ==> ntp4vc_comb3_is_value (NTP4VC_COMB3_App NTP4VC_COMB3_S v)) /\
    (!v1 v2:ntp4vc_comb3_term.
       ntp4vc_comb3_is_value v1 /\ ntp4vc_comb3_is_value v2
       ==> ntp4vc_comb3_is_value
             (NTP4VC_COMB3_App (NTP4VC_COMB3_App NTP4VC_COMB3_S v1) v2))`;;

let ntp4vc_comb3_is_context =
  new_recursive_definition ntp4vc_comb3_context_RECURSION
   `(ntp4vc_comb3_is_context NTP4VC_COMB3_Hole = T) /\
    (!c:ntp4vc_comb3_context.
     !t:ntp4vc_comb3_term.
       ntp4vc_comb3_is_context (NTP4VC_COMB3_Left c t) =
       ntp4vc_comb3_is_context c) /\
    (!v:ntp4vc_comb3_term.
     !c:ntp4vc_comb3_context.
       ntp4vc_comb3_is_context (NTP4VC_COMB3_Right v c) =
       (ntp4vc_comb3_is_value v /\ ntp4vc_comb3_is_context c))`;;

let ntp4vc_comb3_subst =
  new_recursive_definition ntp4vc_comb3_context_RECURSION
   `(!t:ntp4vc_comb3_term.
       ntp4vc_comb3_subst NTP4VC_COMB3_Hole t = t) /\
    (!c:ntp4vc_comb3_context.
     !t2 t:ntp4vc_comb3_term.
       ntp4vc_comb3_subst (NTP4VC_COMB3_Left c t2) t =
       NTP4VC_COMB3_App (ntp4vc_comb3_subst c t) t2) /\
    (!v:ntp4vc_comb3_term.
     !c:ntp4vc_comb3_context.
     !t:ntp4vc_comb3_term.
       ntp4vc_comb3_subst (NTP4VC_COMB3_Right v c) t =
       NTP4VC_COMB3_App v (ntp4vc_comb3_subst c t))`;;

let ntp4vc_comb3_step_RULES,
    ntp4vc_comb3_step_INDUCT,
    ntp4vc_comb3_step_CASES =
  new_inductive_definition
   `(!c:ntp4vc_comb3_context.
     !v1 v2:ntp4vc_comb3_term.
       ntp4vc_comb3_is_context c /\
       ntp4vc_comb3_is_value v1 /\
       ntp4vc_comb3_is_value v2
       ==> ntp4vc_comb3_step
             (ntp4vc_comb3_subst c
               (NTP4VC_COMB3_App
                 (NTP4VC_COMB3_App NTP4VC_COMB3_K v1) v2))
             (ntp4vc_comb3_subst c v1)) /\
    (!c:ntp4vc_comb3_context.
     !v1 v2 v3:ntp4vc_comb3_term.
       ntp4vc_comb3_is_context c /\
       ntp4vc_comb3_is_value v1 /\
       ntp4vc_comb3_is_value v2 /\
       ntp4vc_comb3_is_value v3
       ==> ntp4vc_comb3_step
             (ntp4vc_comb3_subst c
               (NTP4VC_COMB3_App
                 (NTP4VC_COMB3_App
                   (NTP4VC_COMB3_App NTP4VC_COMB3_S v1) v2) v3))
             (ntp4vc_comb3_subst c
               (NTP4VC_COMB3_App
                 (NTP4VC_COMB3_App v1 v3)
                 (NTP4VC_COMB3_App v2 v3))))`;;

let ntp4vc_comb3_reltr_RULES,
    ntp4vc_comb3_reltr_INDUCT,
    ntp4vc_comb3_reltr_CASES =
  new_inductive_definition
   `(!x:ntp4vc_comb3_term.
       ntp4vc_comb3_reltr x x) /\
    (!x y z:ntp4vc_comb3_term.
       ntp4vc_comb3_reltr x y /\ ntp4vc_comb3_step y z
       ==> ntp4vc_comb3_reltr x z)`;;

let ntp4vc_comb3_subst_c =
  new_recursive_definition ntp4vc_comb3_context_RECURSION
   `(!ct:ntp4vc_comb3_context.
       ntp4vc_comb3_subst_c NTP4VC_COMB3_Hole ct = ct) /\
    (!c:ntp4vc_comb3_context.
     !t:ntp4vc_comb3_term.
     !ct:ntp4vc_comb3_context.
       ntp4vc_comb3_subst_c (NTP4VC_COMB3_Left c t) ct =
       NTP4VC_COMB3_Left (ntp4vc_comb3_subst_c c ct) t) /\
    (!v:ntp4vc_comb3_term.
     !c ct:ntp4vc_comb3_context.
       ntp4vc_comb3_subst_c (NTP4VC_COMB3_Right v c) ct =
       NTP4VC_COMB3_Right v (ntp4vc_comb3_subst_c c ct))`;;

let ntp4vc_comb3_ks_nat =
  new_recursive_definition num_RECURSION
   `(ntp4vc_comb3_ks_nat 0 = NTP4VC_COMB3_K) /\
    (!m:num.
       ntp4vc_comb3_ks_nat (SUC m) =
       NTP4VC_COMB3_App (ntp4vc_comb3_ks_nat m) NTP4VC_COMB3_K)`;;

let ntp4vc_comb3_ks = new_definition
 `ntp4vc_comb3_ks (n:int) =
    ntp4vc_comb3_ks_nat (num_of_int n)`;;

let ntp4vc_comb3_even = new_definition
 `ntp4vc_comb3_even (n:int) <=> n rem (&2:int) = (&0:int)`;;

let ntp4vc_comb3_odd = new_definition
 `ntp4vc_comb3_odd (n:int) <=> n rem (&2:int) = (&1:int)`;;

let ntp4vc_comb3_k_head_shape =
  new_recursive_definition ntp4vc_comb3_term_RECURSION
   `(ntp4vc_comb3_k_head_shape NTP4VC_COMB3_S = F) /\
    (ntp4vc_comb3_k_head_shape NTP4VC_COMB3_K = T) /\
    (!f v:ntp4vc_comb3_term.
       ntp4vc_comb3_k_head_shape (NTP4VC_COMB3_App f v) =
       (f = NTP4VC_COMB3_K))`;;

let ntp4vc_comb3_apply_result =
  new_recursive_definition ntp4vc_comb3_term_RECURSION
   `(!v2 result:ntp4vc_comb3_term.
       ntp4vc_comb3_apply_result NTP4VC_COMB3_S v2 result = F) /\
    (!v2 result:ntp4vc_comb3_term.
       ntp4vc_comb3_apply_result NTP4VC_COMB3_K v2 result =
       (result = NTP4VC_COMB3_App NTP4VC_COMB3_K v2)) /\
    (!f v3 v2 result:ntp4vc_comb3_term.
       ntp4vc_comb3_apply_result
         (NTP4VC_COMB3_App f v3) v2 result =
       (f = NTP4VC_COMB3_K /\ result = v3))`;;

let ntp4vc_comb3_initial_case =
  new_recursive_definition ntp4vc_comb3_term_RECURSION
   `(!n:int.
     !c:ntp4vc_comb3_context.
       ntp4vc_comb3_initial_case NTP4VC_COMB3_S n c = F) /\
    (!n:int.
     !c:ntp4vc_comb3_context.
       ntp4vc_comb3_initial_case NTP4VC_COMB3_K n c = T) /\
    (!t1 t2:ntp4vc_comb3_term.
     !n:int.
     !c:ntp4vc_comb3_context.
       ntp4vc_comb3_initial_case (NTP4VC_COMB3_App t1 t2) n c =
       (let o1 = n - (&1:int) in
        let o2 = NTP4VC_COMB3_Left NTP4VC_COMB3_Hole t2 in
        let o3 = ntp4vc_comb3_subst_c c o2 in
        (ntp4vc_comb3_is_context c /\
         ntp4vc_comb3_is_context o2
         ==> ntp4vc_comb3_is_context o3)
        ==>
        ((((&0:int) <= n /\ o1 < n) /\
          (&0:int) <= o1 /\
          t1 = ntp4vc_comb3_ks o1 /\
          ntp4vc_comb3_is_context o3) /\
         (!v1:ntp4vc_comb3_term.
            ntp4vc_comb3_reltr
              (ntp4vc_comb3_subst o3 t1)
              (ntp4vc_comb3_subst o3 v1) /\
            ntp4vc_comb3_is_value v1 /\
            (ntp4vc_comb3_even o1 ==> v1 = NTP4VC_COMB3_K) /\
            (ntp4vc_comb3_odd o1
             ==> v1 = NTP4VC_COMB3_App NTP4VC_COMB3_K NTP4VC_COMB3_K)
            ==>
            let o4 = NTP4VC_COMB3_Right v1 NTP4VC_COMB3_Hole in
            let o5 = ntp4vc_comb3_subst_c c o4 in
            (ntp4vc_comb3_is_context c /\
             ntp4vc_comb3_is_context o4
             ==> ntp4vc_comb3_is_context o5)
            ==>
            ((((&0:int) <= n /\ (&0:int) < n) /\
              (&0:int) <= (&0:int) /\
              t2 = ntp4vc_comb3_ks (&0:int) /\
              ntp4vc_comb3_is_context o5) /\
             (!v2:ntp4vc_comb3_term.
                ntp4vc_comb3_reltr
                  (ntp4vc_comb3_subst o5 t2)
                  (ntp4vc_comb3_subst o5 v2) /\
                ntp4vc_comb3_is_value v2 /\
                (ntp4vc_comb3_even (&0:int)
                 ==> v2 = NTP4VC_COMB3_K) /\
                (ntp4vc_comb3_odd (&0:int)
                 ==> v2 =
                     NTP4VC_COMB3_App NTP4VC_COMB3_K NTP4VC_COMB3_K)
                ==> ntp4vc_comb3_k_head_shape v1))))))`;;

let ntp4vc_comb3_result_case =
  new_recursive_definition ntp4vc_comb3_term_RECURSION
   `(!n:int.
     !c:ntp4vc_comb3_context.
     !result:ntp4vc_comb3_term.
       ntp4vc_comb3_result_case NTP4VC_COMB3_S n c result = F) /\
    (!n:int.
     !c:ntp4vc_comb3_context.
     !result:ntp4vc_comb3_term.
       ntp4vc_comb3_result_case NTP4VC_COMB3_K n c result =
       (result = NTP4VC_COMB3_K)) /\
    (!t1 t2:ntp4vc_comb3_term.
     !n:int.
     !c:ntp4vc_comb3_context.
     !result:ntp4vc_comb3_term.
       ntp4vc_comb3_result_case
         (NTP4VC_COMB3_App t1 t2) n c result =
       (let o1 = n - (&1:int) in
        let o2 = NTP4VC_COMB3_Left NTP4VC_COMB3_Hole t2 in
        let o3 = ntp4vc_comb3_subst_c c o2 in
        (ntp4vc_comb3_is_context c /\
         ntp4vc_comb3_is_context o2
         ==> ntp4vc_comb3_is_context o3) /\
        (?v1:ntp4vc_comb3_term.
           (ntp4vc_comb3_reltr
              (ntp4vc_comb3_subst o3 t1)
              (ntp4vc_comb3_subst o3 v1) /\
            ntp4vc_comb3_is_value v1 /\
            (ntp4vc_comb3_even o1 ==> v1 = NTP4VC_COMB3_K) /\
            (ntp4vc_comb3_odd o1
             ==> v1 = NTP4VC_COMB3_App NTP4VC_COMB3_K NTP4VC_COMB3_K)) /\
           (let o4 = NTP4VC_COMB3_Right v1 NTP4VC_COMB3_Hole in
            let o5 = ntp4vc_comb3_subst_c c o4 in
            (ntp4vc_comb3_is_context c /\
             ntp4vc_comb3_is_context o4
             ==> ntp4vc_comb3_is_context o5) /\
            (?v2:ntp4vc_comb3_term.
               (ntp4vc_comb3_reltr
                  (ntp4vc_comb3_subst o5 t2)
                  (ntp4vc_comb3_subst o5 v2) /\
                ntp4vc_comb3_is_value v2 /\
                (ntp4vc_comb3_even (&0:int)
                 ==> v2 = NTP4VC_COMB3_K) /\
                (ntp4vc_comb3_odd (&0:int)
                 ==> v2 =
                     NTP4VC_COMB3_App NTP4VC_COMB3_K NTP4VC_COMB3_K)) /\
               ntp4vc_comb3_apply_result v1 v2 result)))))`;;

let statement =
 `!n:int.
  !c:ntp4vc_comb3_context.
    (&0:int) <= n
    ==>
    ntp4vc_comb3_is_context c
    ==>
    ntp4vc_comb3_initial_case (ntp4vc_comb3_ks n) n c /\
    (!result:ntp4vc_comb3_term.
       ntp4vc_comb3_result_case (ntp4vc_comb3_ks n) n c result
       ==>
       ntp4vc_comb3_reltr
         (ntp4vc_comb3_subst c (ntp4vc_comb3_ks n))
         (ntp4vc_comb3_subst c result) /\
       ntp4vc_comb3_is_value result /\
       (ntp4vc_comb3_even n ==> result = NTP4VC_COMB3_K) /\
       (ntp4vc_comb3_odd n
        ==> result = NTP4VC_COMB3_App NTP4VC_COMB3_K NTP4VC_COMB3_K))`;;
