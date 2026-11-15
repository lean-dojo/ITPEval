(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_ConcreteInterpreter_interp_exprqtvc: the concrete expression
  interpreter verification condition for integer literals, variable lookup
  including unbound variables, and subtraction. This file contains no proof.
*)

let ntp4vc_imp_expr_INDUCT,ntp4vc_imp_expr_RECURSION = define_type
  "ntp4vc_imp_expr =
       NTP4VC_IMP_Elit int
     | NTP4VC_IMP_Evar A
     | NTP4VC_IMP_Esub ntp4vc_imp_expr ntp4vc_imp_expr";;

let ntp4vc_imp_expr_behaviour_INDUCT,
    ntp4vc_imp_expr_behaviour_RECURSION = define_type
  "ntp4vc_imp_expr_behaviour =
       NTP4VC_IMP_Enormal int
     | NTP4VC_IMP_Eunbound_var";;

let ntp4vc_imp_eval_expr_RULES,
    ntp4vc_imp_eval_expr_INDUCT,
    ntp4vc_imp_eval_expr_CASES =
  new_inductive_definition
   `(!env:A->int option.
     !n:int.
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Elit n) (NTP4VC_IMP_Enormal n)) /\
    (!env:A->int option.
     !x:A.
     !n:int.
       env x = SOME n
       ==>
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Evar x) (NTP4VC_IMP_Enormal n)) /\
    (!env:A->int option.
     !x:A.
       env x = NONE
       ==>
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Evar x) NTP4VC_IMP_Eunbound_var) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_imp_expr.
     !n1 n2:int.
       ntp4vc_imp_eval_expr env e1 (NTP4VC_IMP_Enormal n1) /\
       ntp4vc_imp_eval_expr env e2 (NTP4VC_IMP_Enormal n2)
       ==>
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Esub e1 e2)
         (NTP4VC_IMP_Enormal (n1 - n2))) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_imp_expr.
       ntp4vc_imp_eval_expr env e1 NTP4VC_IMP_Eunbound_var
       ==>
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Esub e1 e2) NTP4VC_IMP_Eunbound_var) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_imp_expr.
     !n1:int.
       ntp4vc_imp_eval_expr env e1 (NTP4VC_IMP_Enormal n1) /\
       ntp4vc_imp_eval_expr env e2 NTP4VC_IMP_Eunbound_var
       ==>
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Esub e1 e2) NTP4VC_IMP_Eunbound_var)`;;

let ntp4vc_imp_interp_expr_vc =
  new_recursive_definition ntp4vc_imp_expr_RECURSION
   `(!env:A->int option.
     !n:int.
       ntp4vc_imp_interp_expr_vc env (NTP4VC_IMP_Elit n) <=>
       ntp4vc_imp_eval_expr
         env (NTP4VC_IMP_Elit n) (NTP4VC_IMP_Enormal n)) /\
    (!env:A->int option.
     !x:A.
       ntp4vc_imp_interp_expr_vc env (NTP4VC_IMP_Evar x) <=>
       ((!result:int.
           env x = SOME result
           ==>
           ntp4vc_imp_eval_expr
             env (NTP4VC_IMP_Evar x) (NTP4VC_IMP_Enormal result)) /\
        (env x = NONE
         ==>
         ntp4vc_imp_eval_expr
           env (NTP4VC_IMP_Evar x) NTP4VC_IMP_Eunbound_var))) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_imp_expr.
       ntp4vc_imp_interp_expr_vc env (NTP4VC_IMP_Esub e1 e2) <=>
       ((e1 = e2 \/ e2 = e2) /\
        (!o1:int.
           ntp4vc_imp_eval_expr env e2 (NTP4VC_IMP_Enormal o1)
           ==>
           (e1 = e1 \/ e2 = e1) /\
           (!o2:int.
              ntp4vc_imp_eval_expr env e1 (NTP4VC_IMP_Enormal o2)
              ==>
              ntp4vc_imp_eval_expr
                env (NTP4VC_IMP_Esub e1 e2)
                (NTP4VC_IMP_Enormal (o2 - o1))) /\
           (ntp4vc_imp_eval_expr env e1 NTP4VC_IMP_Eunbound_var
            ==>
            ntp4vc_imp_eval_expr
              env (NTP4VC_IMP_Esub e1 e2)
              NTP4VC_IMP_Eunbound_var)) /\
        (ntp4vc_imp_eval_expr env e2 NTP4VC_IMP_Eunbound_var
         ==>
         ntp4vc_imp_eval_expr
           env (NTP4VC_IMP_Esub e1 e2)
           NTP4VC_IMP_Eunbound_var)))`;;

let statement =
  `!model1:B->A->int option.
   !e:A ntp4vc_imp_expr.
   !env1:B.
     ntp4vc_imp_interp_expr_vc (model1 env1) e`;;
