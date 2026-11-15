(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_exprqtvc: the symbolic
  expression interpreter verification condition for integer literals,
  variable lookup including unbound variables, and subtraction, together
  with symbolic-variable support. This file contains no proof.
*)

let ntp4vc_sie_expr_INDUCT,ntp4vc_sie_expr_RECURSION = define_type
  "ntp4vc_sie_expr =
       NTP4VC_SIE_Elit int
     | NTP4VC_SIE_Evar A
     | NTP4VC_SIE_Esub ntp4vc_sie_expr ntp4vc_sie_expr";;

let ntp4vc_sie_expr_behavior_INDUCT,
    ntp4vc_sie_expr_behavior_RECURSION = define_type
  "ntp4vc_sie_expr_behavior =
       NTP4VC_SIE_Enormal int
     | NTP4VC_SIE_Eunbound_var";;

let ntp4vc_sie_eval_expr_RULES,
    ntp4vc_sie_eval_expr_INDUCT,
    ntp4vc_sie_eval_expr_CASES =
  new_inductive_definition
   `(!env:A->int option.
     !n:int.
       ntp4vc_sie_eval_expr
         env (NTP4VC_SIE_Elit n) (NTP4VC_SIE_Enormal n)) /\
    (!env:A->int option.
     !x:A.
     !n:int.
       env x = SOME n
       ==>
       ntp4vc_sie_eval_expr
         env (NTP4VC_SIE_Evar x) (NTP4VC_SIE_Enormal n)) /\
    (!env:A->int option.
     !x:A.
       env x = NONE
       ==>
       ntp4vc_sie_eval_expr
         env (NTP4VC_SIE_Evar x) NTP4VC_SIE_Eunbound_var) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_sie_expr.
     !n1 n2:int.
       ntp4vc_sie_eval_expr env e1 (NTP4VC_SIE_Enormal n1) /\
       ntp4vc_sie_eval_expr env e2 (NTP4VC_SIE_Enormal n2)
       ==>
       ntp4vc_sie_eval_expr
         env (NTP4VC_SIE_Esub e1 e2)
         (NTP4VC_SIE_Enormal (n1 - n2))) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_sie_expr.
       ntp4vc_sie_eval_expr env e1 NTP4VC_SIE_Eunbound_var
       ==>
       ntp4vc_sie_eval_expr
         env (NTP4VC_SIE_Esub e1 e2) NTP4VC_SIE_Eunbound_var) /\
    (!env:A->int option.
     !e1 e2:A ntp4vc_sie_expr.
     !n1:int.
       ntp4vc_sie_eval_expr env e1 (NTP4VC_SIE_Enormal n1) /\
       ntp4vc_sie_eval_expr env e2 NTP4VC_SIE_Eunbound_var
       ==>
       ntp4vc_sie_eval_expr
         env (NTP4VC_SIE_Esub e1 e2) NTP4VC_SIE_Eunbound_var)`;;

let ntp4vc_sie_symbolic_expr_INDUCT,
    ntp4vc_sie_symbolic_expr_RECURSION = define_type
  "ntp4vc_sie_symbolic_expr =
       NTP4VC_SIE_Slit int
     | NTP4VC_SIE_Svar B
     | NTP4VC_SIE_Ssub
         ntp4vc_sie_symbolic_expr ntp4vc_sie_symbolic_expr";;

let ntp4vc_sie_constr_INDUCT,ntp4vc_sie_constr_RECURSION = define_type
  "ntp4vc_sie_constr =
       NTP4VC_SIE_Ctrue
     | NTP4VC_SIE_Cfalse
     | NTP4VC_SIE_Ceq
         (B ntp4vc_sie_symbolic_expr)
         (B ntp4vc_sie_symbolic_expr)
     | NTP4VC_SIE_Cneq
         (B ntp4vc_sie_symbolic_expr)
         (B ntp4vc_sie_symbolic_expr)
     | NTP4VC_SIE_Cconj ntp4vc_sie_constr ntp4vc_sie_constr
     | NTP4VC_SIE_Cexists B ntp4vc_sie_constr";;

let ntp4vc_sie_interp_symbolic_expr =
  new_recursive_definition ntp4vc_sie_symbolic_expr_RECURSION
   `(!rho:B->int.
     !n:int.
       ntp4vc_sie_interp_symbolic_expr rho (NTP4VC_SIE_Slit n) = n) /\
    (!rho:B->int.
     !v:B.
       ntp4vc_sie_interp_symbolic_expr rho (NTP4VC_SIE_Svar v) =
       rho v) /\
    (!rho:B->int.
     !e1 e2:B ntp4vc_sie_symbolic_expr.
       ntp4vc_sie_interp_symbolic_expr rho (NTP4VC_SIE_Ssub e1 e2) =
       ntp4vc_sie_interp_symbolic_expr rho e1 -
       ntp4vc_sie_interp_symbolic_expr rho e2)`;;

let ntp4vc_sie_vars_in_symbolic_expr =
  new_recursive_definition ntp4vc_sie_symbolic_expr_RECURSION
   `(!n:int.
       ntp4vc_sie_vars_in_symbolic_expr (NTP4VC_SIE_Slit n) =
       ({}:B->bool)) /\
    (!v:B.
       ntp4vc_sie_vars_in_symbolic_expr (NTP4VC_SIE_Svar v) = {v}) /\
    (!e1 e2:B ntp4vc_sie_symbolic_expr.
       ntp4vc_sie_vars_in_symbolic_expr (NTP4VC_SIE_Ssub e1 e2) =
       ntp4vc_sie_vars_in_symbolic_expr e1 UNION
       ntp4vc_sie_vars_in_symbolic_expr e2)`;;

let ntp4vc_sie_vars_in_constraint =
  new_recursive_definition ntp4vc_sie_constr_RECURSION
   `(ntp4vc_sie_vars_in_constraint NTP4VC_SIE_Ctrue =
      ({}:B->bool)) /\
    (ntp4vc_sie_vars_in_constraint NTP4VC_SIE_Cfalse =
      ({}:B->bool)) /\
    (!e1 e2:B ntp4vc_sie_symbolic_expr.
       ntp4vc_sie_vars_in_constraint (NTP4VC_SIE_Ceq e1 e2) =
       ntp4vc_sie_vars_in_symbolic_expr e1 UNION
       ntp4vc_sie_vars_in_symbolic_expr e2) /\
    (!e1 e2:B ntp4vc_sie_symbolic_expr.
       ntp4vc_sie_vars_in_constraint (NTP4VC_SIE_Cneq e1 e2) =
       ntp4vc_sie_vars_in_symbolic_expr e1 UNION
       ntp4vc_sie_vars_in_symbolic_expr e2) /\
    (!c1 c2:B ntp4vc_sie_constr.
       ntp4vc_sie_vars_in_constraint (NTP4VC_SIE_Cconj c1 c2) =
       ntp4vc_sie_vars_in_constraint c1 UNION
       ntp4vc_sie_vars_in_constraint c2) /\
    (!v:B.
     !c:B ntp4vc_sie_constr.
       ntp4vc_sie_vars_in_constraint (NTP4VC_SIE_Cexists v c) =
       v INSERT ntp4vc_sie_vars_in_constraint c)`;;

let ntp4vc_sie_sym_state_INDUCT,ntp4vc_sie_sym_state_RECURSION =
  define_type
   "ntp4vc_sie_sym_state =
      NTP4VC_SIE_SymState
        (A->B option) (B ntp4vc_sie_constr) (B->int) (B->bool)";;

let ntp4vc_sie_sigma =
  new_recursive_definition ntp4vc_sie_sym_state_RECURSION
   `ntp4vc_sie_sigma (NTP4VC_SIE_SymState sg co r vs) = sg`;;

let ntp4vc_sie_constr =
  new_recursive_definition ntp4vc_sie_sym_state_RECURSION
   `ntp4vc_sie_constr (NTP4VC_SIE_SymState sg co r vs) = co`;;

let ntp4vc_sie_rho =
  new_recursive_definition ntp4vc_sie_sym_state_RECURSION
   `ntp4vc_sie_rho (NTP4VC_SIE_SymState sg co r vs) = r`;;

let ntp4vc_sie_vars =
  new_recursive_definition ntp4vc_sie_sym_state_RECURSION
   `ntp4vc_sie_vars (NTP4VC_SIE_SymState sg co r vs) = vs`;;

let ntp4vc_sie_valid_state = new_definition
  `ntp4vc_sie_valid_state (s:(A,B)ntp4vc_sie_sym_state) <=>
     FINITE (ntp4vc_sie_vars s) /\
     ntp4vc_sie_vars_in_constraint (ntp4vc_sie_constr s)
       SUBSET ntp4vc_sie_vars s /\
     (!x:A.
      !v:B.
        ntp4vc_sie_sigma s x = SOME v
        ==> v IN ntp4vc_sie_vars s)`;;

let ntp4vc_sie_apply_option =
  new_recursive_definition option_RECURSION
   `(!rho:B->int.
       ntp4vc_sie_apply_option rho NONE = NONE) /\
    (!rho:B->int.
     !v:B.
       ntp4vc_sie_apply_option rho (SOME v) = SOME (rho v))`;;

let ntp4vc_sie_compose = new_definition
  `ntp4vc_sie_compose (rho:B->int) (sigma:A->B option) (x:A) =
     ntp4vc_sie_apply_option rho (sigma x)`;;

let ntp4vc_sie_symbolic_expr_supported = new_definition
  `ntp4vc_sie_symbolic_expr_supported
     (sigma:A->B option) (se:B ntp4vc_sie_symbolic_expr) <=>
     !v:B.
       v IN ntp4vc_sie_vars_in_symbolic_expr se
       ==> ?x:A. sigma x = SOME v`;;

let ntp4vc_sie_symbolic_interp_expr_vc =
  new_recursive_definition ntp4vc_sie_expr_RECURSION
   `(!s:(A,B)ntp4vc_sie_sym_state.
     !n:int.
       ntp4vc_sie_symbolic_interp_expr_vc s (NTP4VC_SIE_Elit n) <=>
       ntp4vc_sie_eval_expr
         (ntp4vc_sie_compose (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
         (NTP4VC_SIE_Elit n)
         (NTP4VC_SIE_Enormal
           (ntp4vc_sie_interp_symbolic_expr
             (ntp4vc_sie_rho s) (NTP4VC_SIE_Slit n))) /\
       ntp4vc_sie_symbolic_expr_supported
         (ntp4vc_sie_sigma s) (NTP4VC_SIE_Slit n)) /\
    (!s:(A,B)ntp4vc_sie_sym_state.
     !x:A.
       ntp4vc_sie_symbolic_interp_expr_vc s (NTP4VC_SIE_Evar x) <=>
       ((!o1:B.
           ntp4vc_sie_sigma s x = SOME o1
           ==>
           ntp4vc_sie_eval_expr
             (ntp4vc_sie_compose
               (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
             (NTP4VC_SIE_Evar x)
             (NTP4VC_SIE_Enormal
               (ntp4vc_sie_interp_symbolic_expr
                 (ntp4vc_sie_rho s) (NTP4VC_SIE_Svar o1))) /\
           ntp4vc_sie_symbolic_expr_supported
             (ntp4vc_sie_sigma s) (NTP4VC_SIE_Svar o1)) /\
        (ntp4vc_sie_sigma s x = NONE
         ==>
         ntp4vc_sie_eval_expr
           (ntp4vc_sie_compose
             (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
           (NTP4VC_SIE_Evar x) NTP4VC_SIE_Eunbound_var))) /\
    (!s:(A,B)ntp4vc_sie_sym_state.
     !e1 e2:A ntp4vc_sie_expr.
       ntp4vc_sie_symbolic_interp_expr_vc
         s (NTP4VC_SIE_Esub e1 e2) <=>
       ((e1 = e2 \/ e2 = e2) /\
        (!o1:B ntp4vc_sie_symbolic_expr.
           ntp4vc_sie_eval_expr
             (ntp4vc_sie_compose
               (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
             e2
             (NTP4VC_SIE_Enormal
               (ntp4vc_sie_interp_symbolic_expr
                 (ntp4vc_sie_rho s) o1)) /\
           ntp4vc_sie_symbolic_expr_supported
             (ntp4vc_sie_sigma s) o1
           ==>
           (e1 = e1 \/ e2 = e1) /\
           (!o2:B ntp4vc_sie_symbolic_expr.
              ntp4vc_sie_eval_expr
                (ntp4vc_sie_compose
                  (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
                e1
                (NTP4VC_SIE_Enormal
                  (ntp4vc_sie_interp_symbolic_expr
                    (ntp4vc_sie_rho s) o2)) /\
              ntp4vc_sie_symbolic_expr_supported
                (ntp4vc_sie_sigma s) o2
              ==>
              ntp4vc_sie_eval_expr
                (ntp4vc_sie_compose
                  (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
                (NTP4VC_SIE_Esub e1 e2)
                (NTP4VC_SIE_Enormal
                  (ntp4vc_sie_interp_symbolic_expr
                    (ntp4vc_sie_rho s) (NTP4VC_SIE_Ssub o2 o1))) /\
              ntp4vc_sie_symbolic_expr_supported
                (ntp4vc_sie_sigma s) (NTP4VC_SIE_Ssub o2 o1)) /\
           (ntp4vc_sie_eval_expr
              (ntp4vc_sie_compose
                (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
              e1 NTP4VC_SIE_Eunbound_var
            ==>
            ntp4vc_sie_eval_expr
              (ntp4vc_sie_compose
                (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
              (NTP4VC_SIE_Esub e1 e2) NTP4VC_SIE_Eunbound_var)) /\
        (ntp4vc_sie_eval_expr
           (ntp4vc_sie_compose
             (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
           e2 NTP4VC_SIE_Eunbound_var
         ==>
         ntp4vc_sie_eval_expr
           (ntp4vc_sie_compose
             (ntp4vc_sie_rho s) (ntp4vc_sie_sigma s))
           (NTP4VC_SIE_Esub e1 e2) NTP4VC_SIE_Eunbound_var)))`;;

let statement =
  `!e:A ntp4vc_sie_expr.
   !s:(A,B)ntp4vc_sie_sym_state.
     ntp4vc_sie_valid_state s
     ==> ntp4vc_sie_symbolic_interp_expr_vc s e`;;
