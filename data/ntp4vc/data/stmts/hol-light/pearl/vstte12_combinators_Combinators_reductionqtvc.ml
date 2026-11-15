(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_combinators_Combinators_reductionqtvc: the verification
  condition for recursive call-by-value reduction of S-K combinator terms
  through evaluation contexts to reachable values. This file contains no
  proof.
*)

let ntp4vc_reduction_term_INDUCT,ntp4vc_reduction_term_RECURSION =
  define_type
   "ntp4vc_reduction_term =
        NTP4VC_REDUCTION_S
      | NTP4VC_REDUCTION_K
      | NTP4VC_REDUCTION_App
          ntp4vc_reduction_term ntp4vc_reduction_term";;

let ntp4vc_reduction_context_INDUCT,ntp4vc_reduction_context_RECURSION =
  define_type
   "ntp4vc_reduction_context =
        NTP4VC_REDUCTION_Hole
      | NTP4VC_REDUCTION_Left
          ntp4vc_reduction_context ntp4vc_reduction_term
      | NTP4VC_REDUCTION_Right
          ntp4vc_reduction_term ntp4vc_reduction_context";;

let ntp4vc_reduction_is_value_RULES,
    ntp4vc_reduction_is_value_INDUCT,
    ntp4vc_reduction_is_value_CASES =
  new_inductive_definition
   `(ntp4vc_reduction_is_value NTP4VC_REDUCTION_K) /\
    (ntp4vc_reduction_is_value NTP4VC_REDUCTION_S) /\
    (!v:ntp4vc_reduction_term.
       ntp4vc_reduction_is_value v
       ==> ntp4vc_reduction_is_value
             (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_K v)) /\
    (!v:ntp4vc_reduction_term.
       ntp4vc_reduction_is_value v
       ==> ntp4vc_reduction_is_value
             (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S v)) /\
    (!v1 v2:ntp4vc_reduction_term.
       ntp4vc_reduction_is_value v1 /\
       ntp4vc_reduction_is_value v2
       ==> ntp4vc_reduction_is_value
             (NTP4VC_REDUCTION_App
               (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S v1) v2))`;;

let ntp4vc_reduction_is_context =
  new_recursive_definition ntp4vc_reduction_context_RECURSION
   `(ntp4vc_reduction_is_context NTP4VC_REDUCTION_Hole = T) /\
    (!c:ntp4vc_reduction_context.
     !t:ntp4vc_reduction_term.
       ntp4vc_reduction_is_context (NTP4VC_REDUCTION_Left c t) =
       ntp4vc_reduction_is_context c) /\
    (!v:ntp4vc_reduction_term.
     !c:ntp4vc_reduction_context.
       ntp4vc_reduction_is_context (NTP4VC_REDUCTION_Right v c) =
       (ntp4vc_reduction_is_value v /\
        ntp4vc_reduction_is_context c))`;;

let ntp4vc_reduction_subst =
  new_recursive_definition ntp4vc_reduction_context_RECURSION
   `(!t:ntp4vc_reduction_term.
       ntp4vc_reduction_subst NTP4VC_REDUCTION_Hole t = t) /\
    (!c:ntp4vc_reduction_context.
     !t2 t:ntp4vc_reduction_term.
       ntp4vc_reduction_subst (NTP4VC_REDUCTION_Left c t2) t =
       NTP4VC_REDUCTION_App (ntp4vc_reduction_subst c t) t2) /\
    (!v:ntp4vc_reduction_term.
     !c:ntp4vc_reduction_context.
     !t:ntp4vc_reduction_term.
       ntp4vc_reduction_subst (NTP4VC_REDUCTION_Right v c) t =
       NTP4VC_REDUCTION_App v (ntp4vc_reduction_subst c t))`;;

let ntp4vc_reduction_step_RULES,
    ntp4vc_reduction_step_INDUCT,
    ntp4vc_reduction_step_CASES =
  new_inductive_definition
   `(!c:ntp4vc_reduction_context.
     !v1 v2:ntp4vc_reduction_term.
       ntp4vc_reduction_is_context c /\
       ntp4vc_reduction_is_value v1 /\
       ntp4vc_reduction_is_value v2
       ==> ntp4vc_reduction_step
             (ntp4vc_reduction_subst c
               (NTP4VC_REDUCTION_App
                 (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_K v1) v2))
             (ntp4vc_reduction_subst c v1)) /\
    (!c:ntp4vc_reduction_context.
     !v1 v2 v3:ntp4vc_reduction_term.
       ntp4vc_reduction_is_context c /\
       ntp4vc_reduction_is_value v1 /\
       ntp4vc_reduction_is_value v2 /\
       ntp4vc_reduction_is_value v3
       ==> ntp4vc_reduction_step
             (ntp4vc_reduction_subst c
               (NTP4VC_REDUCTION_App
                 (NTP4VC_REDUCTION_App
                   (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S v1) v2) v3))
             (ntp4vc_reduction_subst c
               (NTP4VC_REDUCTION_App
                 (NTP4VC_REDUCTION_App v1 v3)
                 (NTP4VC_REDUCTION_App v2 v3))))`;;

let ntp4vc_reduction_reltr_RULES,
    ntp4vc_reduction_reltr_INDUCT,
    ntp4vc_reduction_reltr_CASES =
  new_inductive_definition
   `(!x:ntp4vc_reduction_term.
       ntp4vc_reduction_reltr x x) /\
    (!x y z:ntp4vc_reduction_term.
       ntp4vc_reduction_reltr x y /\
       ntp4vc_reduction_step y z
       ==> ntp4vc_reduction_reltr x z)`;;

let ntp4vc_reduction_subst_c =
  new_recursive_definition ntp4vc_reduction_context_RECURSION
   `(!ct:ntp4vc_reduction_context.
       ntp4vc_reduction_subst_c NTP4VC_REDUCTION_Hole ct = ct) /\
    (!c:ntp4vc_reduction_context.
     !t:ntp4vc_reduction_term.
     !ct:ntp4vc_reduction_context.
       ntp4vc_reduction_subst_c (NTP4VC_REDUCTION_Left c t) ct =
       NTP4VC_REDUCTION_Left (ntp4vc_reduction_subst_c c ct) t) /\
    (!v:ntp4vc_reduction_term.
     !c ct:ntp4vc_reduction_context.
       ntp4vc_reduction_subst_c (NTP4VC_REDUCTION_Right v c) ct =
       NTP4VC_REDUCTION_Right v (ntp4vc_reduction_subst_c c ct))`;;

let ntp4vc_reduction_outcome =
  new_recursive_definition ntp4vc_reduction_term_RECURSION
   `(!c:ntp4vc_reduction_context.
     !original v2:ntp4vc_reduction_term.
       ntp4vc_reduction_outcome c original NTP4VC_REDUCTION_S v2 =
       (ntp4vc_reduction_reltr
          (ntp4vc_reduction_subst c original)
          (ntp4vc_reduction_subst c
            (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S v2)) /\
        ntp4vc_reduction_is_value
          (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S v2))) /\
    (!c:ntp4vc_reduction_context.
     !original v2:ntp4vc_reduction_term.
       ntp4vc_reduction_outcome c original NTP4VC_REDUCTION_K v2 =
       (ntp4vc_reduction_reltr
          (ntp4vc_reduction_subst c original)
          (ntp4vc_reduction_subst c
            (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_K v2)) /\
        ntp4vc_reduction_is_value
          (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_K v2))) /\
    (!c:ntp4vc_reduction_context.
     !original f a v2:ntp4vc_reduction_term.
       ntp4vc_reduction_outcome
         c original (NTP4VC_REDUCTION_App f a) v2 =
       ((f = NTP4VC_REDUCTION_S /\
         ntp4vc_reduction_reltr
           (ntp4vc_reduction_subst c original)
           (ntp4vc_reduction_subst c
             (NTP4VC_REDUCTION_App
               (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S a) v2)) /\
         ntp4vc_reduction_is_value
           (NTP4VC_REDUCTION_App
             (NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S a) v2)) \/
        (f = NTP4VC_REDUCTION_K /\
         ntp4vc_reduction_reltr
           (ntp4vc_reduction_subst c original)
           (ntp4vc_reduction_subst c a) /\
         ntp4vc_reduction_is_value a) \/
        (?v3:ntp4vc_reduction_term.
           f = NTP4VC_REDUCTION_App NTP4VC_REDUCTION_S v3 /\
           ntp4vc_reduction_is_context c /\
           (!result:ntp4vc_reduction_term.
              ntp4vc_reduction_reltr
                (ntp4vc_reduction_subst c
                  (NTP4VC_REDUCTION_App
                    (NTP4VC_REDUCTION_App v3 v2)
                    (NTP4VC_REDUCTION_App a v2)))
                (ntp4vc_reduction_subst c result) /\
              ntp4vc_reduction_is_value result
              ==> ntp4vc_reduction_reltr
                    (ntp4vc_reduction_subst c original)
                    (ntp4vc_reduction_subst c result) /\
                  ntp4vc_reduction_is_value result))))`;;

let ntp4vc_reduction_case =
  new_recursive_definition ntp4vc_reduction_term_RECURSION
   `(!c:ntp4vc_reduction_context.
       ntp4vc_reduction_case c NTP4VC_REDUCTION_S =
       (ntp4vc_reduction_reltr
          (ntp4vc_reduction_subst c NTP4VC_REDUCTION_S)
          (ntp4vc_reduction_subst c NTP4VC_REDUCTION_S) /\
        ntp4vc_reduction_is_value NTP4VC_REDUCTION_S)) /\
    (!c:ntp4vc_reduction_context.
       ntp4vc_reduction_case c NTP4VC_REDUCTION_K =
       (ntp4vc_reduction_reltr
          (ntp4vc_reduction_subst c NTP4VC_REDUCTION_K)
          (ntp4vc_reduction_subst c NTP4VC_REDUCTION_K) /\
        ntp4vc_reduction_is_value NTP4VC_REDUCTION_K)) /\
    (!c:ntp4vc_reduction_context.
     !t1 t2:ntp4vc_reduction_term.
       ntp4vc_reduction_case c (NTP4VC_REDUCTION_App t1 t2) =
       (let o1 =
          NTP4VC_REDUCTION_Left NTP4VC_REDUCTION_Hole t2 in
        let o2 = ntp4vc_reduction_subst_c c o1 in
        (ntp4vc_reduction_is_context c /\
         ntp4vc_reduction_is_context o1
         ==> ntp4vc_reduction_is_context o2)
        ==>
        ntp4vc_reduction_is_context o2 /\
        (!v1:ntp4vc_reduction_term.
           ntp4vc_reduction_reltr
             (ntp4vc_reduction_subst o2 t1)
             (ntp4vc_reduction_subst o2 v1) /\
           ntp4vc_reduction_is_value v1
           ==>
           (let o3 =
              NTP4VC_REDUCTION_Right v1 NTP4VC_REDUCTION_Hole in
            let o4 = ntp4vc_reduction_subst_c c o3 in
            (ntp4vc_reduction_is_context c /\
             ntp4vc_reduction_is_context o3
             ==> ntp4vc_reduction_is_context o4)
            ==>
            ntp4vc_reduction_is_context o4 /\
            (!v2:ntp4vc_reduction_term.
               ntp4vc_reduction_reltr
                 (ntp4vc_reduction_subst o4 t2)
                 (ntp4vc_reduction_subst o4 v2) /\
               ntp4vc_reduction_is_value v2
               ==> ntp4vc_reduction_outcome
                     c (NTP4VC_REDUCTION_App t1 t2) v1 v2)))))`;;

let statement =
  `!c:ntp4vc_reduction_context.
   !t:ntp4vc_reduction_term.
     ntp4vc_reduction_is_context c
     ==> ntp4vc_reduction_case c t`;;
