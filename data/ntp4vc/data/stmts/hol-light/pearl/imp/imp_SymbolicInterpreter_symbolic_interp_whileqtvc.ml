(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_whileqtvc: the
  verification condition for symbolic interpretation of a bounded IMP
  while-loop, including symbolic guard branches, state extension, result
  soundness and completeness, and loop-counter decrease. This file contains
  no proof.
*)

let ntp4vc_siwl_expr_INDUCT,ntp4vc_siwl_expr_RECURSION = define_type
  "ntp4vc_siwl_expr =
       NTP4VC_SIWL_Elit int
     | NTP4VC_SIWL_Evar A
     | NTP4VC_SIWL_Esub ntp4vc_siwl_expr ntp4vc_siwl_expr";;

let ntp4vc_siwl_cmd_INDUCT,ntp4vc_siwl_cmd_RECURSION = define_type
  "ntp4vc_siwl_cmd =
       NTP4VC_SIWL_Cskip
     | NTP4VC_SIWL_Cassign A (A ntp4vc_siwl_expr)
     | NTP4VC_SIWL_Cseq ntp4vc_siwl_cmd ntp4vc_siwl_cmd
     | NTP4VC_SIWL_Cif
         (A ntp4vc_siwl_expr) ntp4vc_siwl_cmd ntp4vc_siwl_cmd
     | NTP4VC_SIWL_Cwhile (A ntp4vc_siwl_expr) ntp4vc_siwl_cmd";;

let ntp4vc_siwl_expr_behavior_INDUCT,
    ntp4vc_siwl_expr_behavior_RECURSION = define_type
  "ntp4vc_siwl_expr_behavior =
       NTP4VC_SIWL_Enormal int
     | NTP4VC_SIWL_Eunbound_var";;

let ntp4vc_siwl_behavior_INDUCT,ntp4vc_siwl_behavior_RECURSION = define_type
  "ntp4vc_siwl_behavior =
       NTP4VC_SIWL_Cnormal
     | NTP4VC_SIWL_Cunbound_var
     | NTP4VC_SIWL_Cloop_limit";;

let ntp4vc_siwl_config_INDUCT,ntp4vc_siwl_config_RECURSION = define_type
  "ntp4vc_siwl_config =
       NTP4VC_SIWL_No_limit
     | NTP4VC_SIWL_Loop_limit num";;

let ntp4vc_siwl_mk_loop_cnf = new_definition
  `ntp4vc_siwl_mk_loop_cnf (n:int) =
     NTP4VC_SIWL_Loop_limit (num_of_int n)`;;

let ntp4vc_siwl_under_limit =
  new_recursive_definition ntp4vc_siwl_config_RECURSION
   `(!ctr:int.
       ntp4vc_siwl_under_limit NTP4VC_SIWL_No_limit ctr <=> T) /\
    (!n:num. !ctr:int.
       ntp4vc_siwl_under_limit (NTP4VC_SIWL_Loop_limit n) ctr <=>
       ctr < &n)`;;

let ntp4vc_siwl_at_limit =
  new_recursive_definition ntp4vc_siwl_config_RECURSION
   `(!ctr:int.
       ntp4vc_siwl_at_limit NTP4VC_SIWL_No_limit ctr <=> F) /\
    (!n:num. !ctr:int.
       ntp4vc_siwl_at_limit (NTP4VC_SIWL_Loop_limit n) ctr <=>
       &n <= ctr)`;;

let ntp4vc_siwl_update = new_definition
  `ntp4vc_siwl_update (env:A->int option) (v:A) (n:int) =
     \x. if x = v then SOME n else env x`;;

let ntp4vc_siwl_eval_expr_RULES,
    ntp4vc_siwl_eval_expr_INDUCT,
    ntp4vc_siwl_eval_expr_CASES =
  new_inductive_definition
   `(!env:A->int option. !n:int.
       ntp4vc_siwl_eval_expr
         env (NTP4VC_SIWL_Elit n) (NTP4VC_SIWL_Enormal n)) /\
    (!env:A->int option. !x:A. !n:int.
       env x = SOME n
       ==> ntp4vc_siwl_eval_expr
             env (NTP4VC_SIWL_Evar x) (NTP4VC_SIWL_Enormal n)) /\
    (!env:A->int option. !x:A.
       env x = NONE
       ==> ntp4vc_siwl_eval_expr
             env (NTP4VC_SIWL_Evar x) NTP4VC_SIWL_Eunbound_var) /\
    (!env:A->int option. !e1 e2:A ntp4vc_siwl_expr. !n1 n2:int.
       ntp4vc_siwl_eval_expr env e1 (NTP4VC_SIWL_Enormal n1) /\
       ntp4vc_siwl_eval_expr env e2 (NTP4VC_SIWL_Enormal n2)
       ==> ntp4vc_siwl_eval_expr
             env (NTP4VC_SIWL_Esub e1 e2)
             (NTP4VC_SIWL_Enormal (n1 - n2))) /\
    (!env:A->int option. !e1 e2:A ntp4vc_siwl_expr.
       ntp4vc_siwl_eval_expr env e1 NTP4VC_SIWL_Eunbound_var
       ==> ntp4vc_siwl_eval_expr
             env (NTP4VC_SIWL_Esub e1 e2)
             NTP4VC_SIWL_Eunbound_var) /\
    (!env:A->int option. !e1 e2:A ntp4vc_siwl_expr. !n1:int.
       ntp4vc_siwl_eval_expr env e1 (NTP4VC_SIWL_Enormal n1) /\
       ntp4vc_siwl_eval_expr env e2 NTP4VC_SIWL_Eunbound_var
       ==> ntp4vc_siwl_eval_expr
             env (NTP4VC_SIWL_Esub e1 e2)
             NTP4VC_SIWL_Eunbound_var)`;;

let ntp4vc_siwl_exec_RULES,
    ntp4vc_siwl_exec_INDUCT,
    ntp4vc_siwl_exec_CASES =
  new_inductive_definition
   `(!cnf:ntp4vc_siwl_config. !env:A->int option.
       ntp4vc_siwl_exec_cmd
         cnf env NTP4VC_SIWL_Cskip env NTP4VC_SIWL_Cnormal) /\
    (!cnf:ntp4vc_siwl_config. !env:A->int option.
     !v:A. !e:A ntp4vc_siwl_expr. !n:int.
       ntp4vc_siwl_eval_expr env e (NTP4VC_SIWL_Enormal n)
       ==> ntp4vc_siwl_exec_cmd cnf env
             (NTP4VC_SIWL_Cassign v e)
             (ntp4vc_siwl_update env v n)
             NTP4VC_SIWL_Cnormal) /\
    (!cnf:ntp4vc_siwl_config. !env:A->int option.
     !v:A. !e:A ntp4vc_siwl_expr.
       ntp4vc_siwl_eval_expr env e NTP4VC_SIWL_Eunbound_var
       ==> ntp4vc_siwl_exec_cmd cnf env
             (NTP4VC_SIWL_Cassign v e) env NTP4VC_SIWL_Cunbound_var) /\
    (!cnf:ntp4vc_siwl_config.
     !env1 env2 env3:A->int option.
     !c1 c2:A ntp4vc_siwl_cmd. !bhv:ntp4vc_siwl_behavior.
       ntp4vc_siwl_exec_cmd cnf env1 c1 env2 NTP4VC_SIWL_Cnormal /\
       ntp4vc_siwl_exec_cmd cnf env2 c2 env3 bhv
       ==> ntp4vc_siwl_exec_cmd
             cnf env1 (NTP4VC_SIWL_Cseq c1 c2) env3 bhv) /\
    (!cnf:ntp4vc_siwl_config. !env1 env2:A->int option.
     !c1 c2:A ntp4vc_siwl_cmd. !bhv:ntp4vc_siwl_behavior.
       ntp4vc_siwl_exec_cmd cnf env1 c1 env2 bhv /\
       ~(bhv = NTP4VC_SIWL_Cnormal)
       ==> ntp4vc_siwl_exec_cmd
             cnf env1 (NTP4VC_SIWL_Cseq c1 c2) env2 bhv) /\
    (!cnf:ntp4vc_siwl_config. !env env':A->int option.
     !e:A ntp4vc_siwl_expr. !c1 c2:A ntp4vc_siwl_cmd.
     !bhv:ntp4vc_siwl_behavior.
       ntp4vc_siwl_eval_expr env e (NTP4VC_SIWL_Enormal (&0)) /\
       ntp4vc_siwl_exec_cmd cnf env c2 env' bhv
       ==> ntp4vc_siwl_exec_cmd
             cnf env (NTP4VC_SIWL_Cif e c1 c2) env' bhv) /\
    (!cnf:ntp4vc_siwl_config. !env env':A->int option.
     !e:A ntp4vc_siwl_expr. !c1 c2:A ntp4vc_siwl_cmd.
     !n:int. !bhv:ntp4vc_siwl_behavior.
       ~(n = &0) /\
       ntp4vc_siwl_eval_expr env e (NTP4VC_SIWL_Enormal n) /\
       ntp4vc_siwl_exec_cmd cnf env c1 env' bhv
       ==> ntp4vc_siwl_exec_cmd
             cnf env (NTP4VC_SIWL_Cif e c1 c2) env' bhv) /\
    (!cnf:ntp4vc_siwl_config. !env:A->int option.
     !e:A ntp4vc_siwl_expr. !c1 c2:A ntp4vc_siwl_cmd.
       ntp4vc_siwl_eval_expr env e NTP4VC_SIWL_Eunbound_var
       ==> ntp4vc_siwl_exec_cmd cnf env
             (NTP4VC_SIWL_Cif e c1 c2)
             env NTP4VC_SIWL_Cunbound_var) /\
    (!cnf:ntp4vc_siwl_config. !env env':A->int option.
     !e:A ntp4vc_siwl_expr. !c:A ntp4vc_siwl_cmd.
     !bhv:ntp4vc_siwl_behavior.
       ntp4vc_siwl_exec_while cnf (&0) env e c env' bhv
       ==> ntp4vc_siwl_exec_cmd
             cnf env (NTP4VC_SIWL_Cwhile e c) env' bhv) /\
    (!cnf:ntp4vc_siwl_config. !ctr:int. !env:A->int option.
     !e:A ntp4vc_siwl_expr. !c:A ntp4vc_siwl_cmd.
       ntp4vc_siwl_at_limit cnf ctr
       ==> ntp4vc_siwl_exec_while
             cnf ctr env e c env NTP4VC_SIWL_Cloop_limit) /\
    (!cnf:ntp4vc_siwl_config. !ctr:int. !env:A->int option.
     !e:A ntp4vc_siwl_expr. !c:A ntp4vc_siwl_cmd.
       ntp4vc_siwl_under_limit cnf ctr /\
       ntp4vc_siwl_eval_expr env e (NTP4VC_SIWL_Enormal (&0))
       ==> ntp4vc_siwl_exec_while
             cnf ctr env e c env NTP4VC_SIWL_Cnormal) /\
    (!cnf:ntp4vc_siwl_config. !ctr:int. !env:A->int option.
     !e:A ntp4vc_siwl_expr. !c:A ntp4vc_siwl_cmd.
       ntp4vc_siwl_under_limit cnf ctr /\
       ntp4vc_siwl_eval_expr env e NTP4VC_SIWL_Eunbound_var
       ==> ntp4vc_siwl_exec_while
             cnf ctr env e c env NTP4VC_SIWL_Cunbound_var) /\
    (!cnf:ntp4vc_siwl_config. !ctr:int.
     !env1 env2:A->int option.
     !e:A ntp4vc_siwl_expr. !c:A ntp4vc_siwl_cmd.
     !v:int. !bhv:ntp4vc_siwl_behavior.
       ntp4vc_siwl_under_limit cnf ctr /\
       ntp4vc_siwl_eval_expr env1 e (NTP4VC_SIWL_Enormal v) /\
       ~(v = &0) /\
       ntp4vc_siwl_exec_cmd cnf env1 c env2 bhv /\
       ~(bhv = NTP4VC_SIWL_Cnormal)
       ==> ntp4vc_siwl_exec_while cnf ctr env1 e c env2 bhv) /\
    (!cnf:ntp4vc_siwl_config. !ctr:int.
     !env1 env2 env3:A->int option.
     !e:A ntp4vc_siwl_expr. !c:A ntp4vc_siwl_cmd.
     !v:int. !bhv:ntp4vc_siwl_behavior.
       ntp4vc_siwl_under_limit cnf ctr /\
       ntp4vc_siwl_eval_expr env1 e (NTP4VC_SIWL_Enormal v) /\
       ~(v = &0) /\
       ntp4vc_siwl_exec_cmd cnf env1 c env2 NTP4VC_SIWL_Cnormal /\
       ntp4vc_siwl_exec_while cnf (ctr + &1) env2 e c env3 bhv
       ==> ntp4vc_siwl_exec_while cnf ctr env1 e c env3 bhv)`;;

let ntp4vc_siwl_symbolic_expr_INDUCT,
    ntp4vc_siwl_symbolic_expr_RECURSION = define_type
  "ntp4vc_siwl_symbolic_expr =
       NTP4VC_SIWL_Slit int
     | NTP4VC_SIWL_Svar B
     | NTP4VC_SIWL_Ssub
         ntp4vc_siwl_symbolic_expr ntp4vc_siwl_symbolic_expr";;

let ntp4vc_siwl_constr_INDUCT,ntp4vc_siwl_constr_RECURSION = define_type
  "ntp4vc_siwl_constr =
       NTP4VC_SIWL_Ctrue
     | NTP4VC_SIWL_Cfalse
     | NTP4VC_SIWL_Ceq
         (B ntp4vc_siwl_symbolic_expr)
         (B ntp4vc_siwl_symbolic_expr)
     | NTP4VC_SIWL_Cneq
         (B ntp4vc_siwl_symbolic_expr)
         (B ntp4vc_siwl_symbolic_expr)
     | NTP4VC_SIWL_Cconj ntp4vc_siwl_constr ntp4vc_siwl_constr
     | NTP4VC_SIWL_Cexists B ntp4vc_siwl_constr";;

let ntp4vc_siwl_interp_symbolic_expr =
  new_recursive_definition ntp4vc_siwl_symbolic_expr_RECURSION
   `(!rho:B->int. !n:int.
       ntp4vc_siwl_interp_symbolic_expr rho (NTP4VC_SIWL_Slit n) = n) /\
    (!rho:B->int. !v:B.
       ntp4vc_siwl_interp_symbolic_expr rho (NTP4VC_SIWL_Svar v) =
       rho v) /\
    (!rho:B->int. !e1 e2:B ntp4vc_siwl_symbolic_expr.
       ntp4vc_siwl_interp_symbolic_expr rho (NTP4VC_SIWL_Ssub e1 e2) =
       ntp4vc_siwl_interp_symbolic_expr rho e1 -
       ntp4vc_siwl_interp_symbolic_expr rho e2)`;;

let ntp4vc_siwl_is_solution =
  new_recursive_definition ntp4vc_siwl_constr_RECURSION
   `(!rho:B->int.
       ntp4vc_siwl_is_solution rho NTP4VC_SIWL_Ctrue <=> T) /\
    (!rho:B->int.
       ntp4vc_siwl_is_solution rho NTP4VC_SIWL_Cfalse <=> F) /\
    (!rho:B->int. !e1 e2:B ntp4vc_siwl_symbolic_expr.
       ntp4vc_siwl_is_solution rho (NTP4VC_SIWL_Ceq e1 e2) <=>
       ntp4vc_siwl_interp_symbolic_expr rho e1 =
       ntp4vc_siwl_interp_symbolic_expr rho e2) /\
    (!rho:B->int. !e1 e2:B ntp4vc_siwl_symbolic_expr.
       ntp4vc_siwl_is_solution rho (NTP4VC_SIWL_Cneq e1 e2) <=>
       ~(ntp4vc_siwl_interp_symbolic_expr rho e1 =
         ntp4vc_siwl_interp_symbolic_expr rho e2)) /\
    (!rho:B->int. !c1 c2:B ntp4vc_siwl_constr.
       ntp4vc_siwl_is_solution rho (NTP4VC_SIWL_Cconj c1 c2) <=>
       ntp4vc_siwl_is_solution rho c1 /\
       ntp4vc_siwl_is_solution rho c2) /\
    (!rho:B->int. !v:B. !c:B ntp4vc_siwl_constr.
       ntp4vc_siwl_is_solution rho (NTP4VC_SIWL_Cexists v c) <=>
       ntp4vc_siwl_is_solution rho c)`;;

let ntp4vc_siwl_vars_in_symbolic_expr =
  new_recursive_definition ntp4vc_siwl_symbolic_expr_RECURSION
   `(!n:int.
       ntp4vc_siwl_vars_in_symbolic_expr (NTP4VC_SIWL_Slit n) =
       ({}:B->bool)) /\
    (!v:B.
       ntp4vc_siwl_vars_in_symbolic_expr (NTP4VC_SIWL_Svar v) = {v}) /\
    (!e1 e2:B ntp4vc_siwl_symbolic_expr.
       ntp4vc_siwl_vars_in_symbolic_expr (NTP4VC_SIWL_Ssub e1 e2) =
       ntp4vc_siwl_vars_in_symbolic_expr e1 UNION
       ntp4vc_siwl_vars_in_symbolic_expr e2)`;;

let ntp4vc_siwl_vars_in_constraint =
  new_recursive_definition ntp4vc_siwl_constr_RECURSION
   `(ntp4vc_siwl_vars_in_constraint NTP4VC_SIWL_Ctrue =
      ({}:B->bool)) /\
    (ntp4vc_siwl_vars_in_constraint NTP4VC_SIWL_Cfalse =
      ({}:B->bool)) /\
    (!e1 e2:B ntp4vc_siwl_symbolic_expr.
       ntp4vc_siwl_vars_in_constraint (NTP4VC_SIWL_Ceq e1 e2) =
       ntp4vc_siwl_vars_in_symbolic_expr e1 UNION
       ntp4vc_siwl_vars_in_symbolic_expr e2) /\
    (!e1 e2:B ntp4vc_siwl_symbolic_expr.
       ntp4vc_siwl_vars_in_constraint (NTP4VC_SIWL_Cneq e1 e2) =
       ntp4vc_siwl_vars_in_symbolic_expr e1 UNION
       ntp4vc_siwl_vars_in_symbolic_expr e2) /\
    (!c1 c2:B ntp4vc_siwl_constr.
       ntp4vc_siwl_vars_in_constraint (NTP4VC_SIWL_Cconj c1 c2) =
       ntp4vc_siwl_vars_in_constraint c1 UNION
       ntp4vc_siwl_vars_in_constraint c2) /\
    (!v:B. !c:B ntp4vc_siwl_constr.
       ntp4vc_siwl_vars_in_constraint (NTP4VC_SIWL_Cexists v c) =
       v INSERT ntp4vc_siwl_vars_in_constraint c)`;;

let ntp4vc_siwl_sym_state_INDUCT,ntp4vc_siwl_sym_state_RECURSION =
  define_type
   "ntp4vc_siwl_sym_state =
      NTP4VC_SIWL_SymState
        (A->B option) (B ntp4vc_siwl_constr) (B->int) (B->bool)";;

let ntp4vc_siwl_sigma =
  new_recursive_definition ntp4vc_siwl_sym_state_RECURSION
   `ntp4vc_siwl_sigma (NTP4VC_SIWL_SymState sg co r vs) = sg`;;

let ntp4vc_siwl_constr =
  new_recursive_definition ntp4vc_siwl_sym_state_RECURSION
   `ntp4vc_siwl_constr (NTP4VC_SIWL_SymState sg co r vs) = co`;;

let ntp4vc_siwl_rho =
  new_recursive_definition ntp4vc_siwl_sym_state_RECURSION
   `ntp4vc_siwl_rho (NTP4VC_SIWL_SymState sg co r vs) = r`;;

let ntp4vc_siwl_vars =
  new_recursive_definition ntp4vc_siwl_sym_state_RECURSION
   `ntp4vc_siwl_vars (NTP4VC_SIWL_SymState sg co r vs) = vs`;;

let ntp4vc_siwl_valid_state = new_definition
  `ntp4vc_siwl_valid_state (s:(A,B)ntp4vc_siwl_sym_state) <=>
     FINITE (ntp4vc_siwl_vars s) /\
     ntp4vc_siwl_vars_in_constraint (ntp4vc_siwl_constr s)
       SUBSET ntp4vc_siwl_vars s /\
     (!x:A. !v:B.
        ntp4vc_siwl_sigma s x = SOME v
        ==> v IN ntp4vc_siwl_vars s)`;;

let ntp4vc_siwl_sym_state_set_INDUCT,
    ntp4vc_siwl_sym_state_set_RECURSION = define_type
  "ntp4vc_siwl_sym_state_set =
     NTP4VC_SIWL_SymStateSet ((A,B)ntp4vc_siwl_sym_state)list";;

let ntp4vc_siwl_to_set =
  new_recursive_definition ntp4vc_siwl_sym_state_set_RECURSION
   `ntp4vc_siwl_to_set (NTP4VC_SIWL_SymStateSet xs) =
      {s | ntp4vc_siwl_valid_state s /\ MEM s xs}`;;

let ntp4vc_siwl_apply_option =
  new_recursive_definition option_RECURSION
   `(!r:B->int.
       ntp4vc_siwl_apply_option r NONE = NONE) /\
    (!r:B->int. !v:B.
       ntp4vc_siwl_apply_option r (SOME v) = SOME (r v))`;;

let ntp4vc_siwl_compose = new_definition
  `ntp4vc_siwl_compose (r:B->int) (sg:A->B option) (x:A) =
     ntp4vc_siwl_apply_option r (sg x)`;;

let ntp4vc_siwl_state_extends = new_definition
  `ntp4vc_siwl_state_extends
     (s:(A,B)ntp4vc_siwl_sym_state)
     (s':(A,B)ntp4vc_siwl_sym_state) <=>
     ntp4vc_siwl_vars s SUBSET ntp4vc_siwl_vars s' /\
     (!v:B.
        v IN ntp4vc_siwl_vars s
        ==> ntp4vc_siwl_rho s v = ntp4vc_siwl_rho s' v)`;;

let ntp4vc_siwl_results_extend = new_definition
  `ntp4vc_siwl_results_extend
     (s:(A,B)ntp4vc_siwl_sym_state)
     (normals:(A,B)ntp4vc_siwl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_siwl_sym_state->bool)
     (limits:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     !s':(A,B)ntp4vc_siwl_sym_state.
       s' IN normals \/ s' IN unbounds \/ s' IN limits
       ==> ntp4vc_siwl_state_extends s s'`;;

let ntp4vc_siwl_in_results = new_definition
  `ntp4vc_siwl_in_results
     (bhv:ntp4vc_siwl_behavior)
     (s:(A,B)ntp4vc_siwl_sym_state)
     (normals:(A,B)ntp4vc_siwl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_siwl_sym_state->bool)
     (limits:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     (bhv = NTP4VC_SIWL_Cnormal /\ s IN normals) \/
     (bhv = NTP4VC_SIWL_Cunbound_var /\ s IN unbounds) \/
     (bhv = NTP4VC_SIWL_Cloop_limit /\ s IN limits)`;;

let ntp4vc_siwl_to_list =
  new_recursive_definition ntp4vc_siwl_sym_state_set_RECURSION
   `ntp4vc_siwl_to_list (NTP4VC_SIWL_SymStateSet xs) =
      FILTER ntp4vc_siwl_valid_state xs`;;

let ntp4vc_siwl_symbolic_expr_supported = new_definition
  `ntp4vc_siwl_symbolic_expr_supported
     (sg:A->B option) (se:B ntp4vc_siwl_symbolic_expr) <=>
     !v:B.
       v IN ntp4vc_siwl_vars_in_symbolic_expr se
       ==> ?x:A. sg x = SOME v`;;

let ntp4vc_siwl_store_supported = new_definition
  `ntp4vc_siwl_store_supported (sg:A->B option) (vs:B->bool) <=>
     !x:A. !v:B. sg x = SOME v ==> v IN vs`;;

let ntp4vc_siwl_state_has_fields = new_definition
  `ntp4vc_siwl_state_has_fields
     (s:(A,B)ntp4vc_siwl_sym_state)
     (sg:A->B option)
     (co:B ntp4vc_siwl_constr)
     (r:B->int)
     (vs:B->bool) <=>
     ntp4vc_siwl_valid_state s /\
     ntp4vc_siwl_sigma s = sg /\
     ntp4vc_siwl_constr s = co /\
     ntp4vc_siwl_rho s = r /\
     ntp4vc_siwl_vars s = vs`;;

let ntp4vc_siwl_empty_result = new_definition
  `ntp4vc_siwl_empty_result
     (xs:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     xs = {} /\ &(CARD xs) = (&0:int)`;;

let ntp4vc_siwl_single_result = new_definition
  `ntp4vc_siwl_single_result
     (xs:(A,B)ntp4vc_siwl_sym_state->bool)
     (s:(A,B)ntp4vc_siwl_sym_state) <=>
     xs = {s} /\ &(CARD xs) = (&1:int)`;;

let ntp4vc_siwl_good_cmd_results = new_definition
  `ntp4vc_siwl_good_cmd_results
     (n:int)
     (s:(A,B)ntp4vc_siwl_sym_state)
     (c:A ntp4vc_siwl_cmd)
     (normals:(A,B)ntp4vc_siwl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_siwl_sym_state->bool)
     (limits:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     ntp4vc_siwl_results_extend s normals unbounds limits /\
     (ntp4vc_siwl_is_solution
        (ntp4vc_siwl_rho s) (ntp4vc_siwl_constr s)
      ==>
      !gamma':A->int option. !bhv:ntp4vc_siwl_behavior.
        ntp4vc_siwl_exec_cmd (ntp4vc_siwl_mk_loop_cnf n)
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
          c gamma' bhv
        ==>
        ?s':(A,B)ntp4vc_siwl_sym_state.
          ntp4vc_siwl_in_results bhv s' normals unbounds limits /\
          ntp4vc_siwl_is_solution
            (ntp4vc_siwl_rho s') (ntp4vc_siwl_constr s') /\
          gamma' =
          ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s') (ntp4vc_siwl_sigma s')) /\
     (!bhv:ntp4vc_siwl_behavior.
      !s':(A,B)ntp4vc_siwl_sym_state.
        ntp4vc_siwl_in_results bhv s' normals unbounds limits
        ==>
        ntp4vc_siwl_is_solution
          (ntp4vc_siwl_rho s') (ntp4vc_siwl_constr s')
        ==>
        ntp4vc_siwl_is_solution
          (ntp4vc_siwl_rho s) (ntp4vc_siwl_constr s) /\
        ntp4vc_siwl_exec_cmd (ntp4vc_siwl_mk_loop_cnf n)
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
          c
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s') (ntp4vc_siwl_sigma s'))
          bhv)`;;

let ntp4vc_siwl_good_while_results = new_definition
  `ntp4vc_siwl_good_while_results
     (n:int) (ctr:int)
     (s:(A,B)ntp4vc_siwl_sym_state)
     (e:A ntp4vc_siwl_expr)
     (c:A ntp4vc_siwl_cmd)
     (normals:(A,B)ntp4vc_siwl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_siwl_sym_state->bool)
     (limits:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     ntp4vc_siwl_results_extend s normals unbounds limits /\
     (ntp4vc_siwl_is_solution
        (ntp4vc_siwl_rho s) (ntp4vc_siwl_constr s)
      ==>
      !gamma':A->int option. !bhv:ntp4vc_siwl_behavior.
        ntp4vc_siwl_exec_while (ntp4vc_siwl_mk_loop_cnf n) ctr
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
          e c gamma' bhv
        ==>
        ?s':(A,B)ntp4vc_siwl_sym_state.
          ntp4vc_siwl_in_results bhv s' normals unbounds limits /\
          ntp4vc_siwl_is_solution
            (ntp4vc_siwl_rho s') (ntp4vc_siwl_constr s') /\
          gamma' =
          ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s') (ntp4vc_siwl_sigma s')) /\
     (!bhv:ntp4vc_siwl_behavior.
      !s':(A,B)ntp4vc_siwl_sym_state.
        ntp4vc_siwl_in_results bhv s' normals unbounds limits
        ==>
        ntp4vc_siwl_is_solution
          (ntp4vc_siwl_rho s') (ntp4vc_siwl_constr s')
        ==>
        ntp4vc_siwl_is_solution
          (ntp4vc_siwl_rho s) (ntp4vc_siwl_constr s) /\
        ntp4vc_siwl_exec_while (ntp4vc_siwl_mk_loop_cnf n) ctr
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
          e c
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s') (ntp4vc_siwl_sigma s'))
          bhv)`;;

let ntp4vc_siwl_body_branch_results = new_definition
  `ntp4vc_siwl_body_branch_results
     (n:int) (ctr:int)
     (s1:(A,B)ntp4vc_siwl_sym_state)
     (e:A ntp4vc_siwl_expr)
     (c:A ntp4vc_siwl_cmd)
     (normals1:(A,B)ntp4vc_siwl_sym_state->bool)
     (unbounds1:(A,B)ntp4vc_siwl_sym_state->bool)
     (limits1:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     ?flag:bool.
       (~flag
        ==> !r:B->int.
              ~ntp4vc_siwl_is_solution r (ntp4vc_siwl_constr s1)) /\
       ((flag /\
         ?normals2 unbounds2 limits2:
            (A,B)ntp4vc_siwl_sym_state_set.
           ntp4vc_siwl_good_cmd_results n s1 c
             (ntp4vc_siwl_to_set normals2)
             (ntp4vc_siwl_to_set unbounds2)
             (ntp4vc_siwl_to_set limits2) /\
           let o2 = ntp4vc_siwl_to_list normals2 in
           (!x:(A,B)ntp4vc_siwl_sym_state.
              x IN ntp4vc_siwl_to_set normals2 <=> MEM x o2) /\
           let o3 = ctr + (&1:int) in
           ?unbounds3 limits3:(A,B)ntp4vc_siwl_sym_state_set.
             (!s':(A,B)ntp4vc_siwl_sym_state.
                s' IN normals1 \/
                s' IN ntp4vc_siwl_to_set unbounds3 \/
                s' IN ntp4vc_siwl_to_set limits3
                ==>
                ?s3:(A,B)ntp4vc_siwl_sym_state.
                  s3 IN ntp4vc_siwl_to_set
                    (NTP4VC_SIWL_SymStateSet o2) /\
                  ntp4vc_siwl_state_extends s3 s') /\
             (!s3:(A,B)ntp4vc_siwl_sym_state.
                s3 IN ntp4vc_siwl_to_set
                  (NTP4VC_SIWL_SymStateSet o2)
                ==>
                ntp4vc_siwl_is_solution
                  (ntp4vc_siwl_rho s3) (ntp4vc_siwl_constr s3)
                ==>
                !gamma':A->int option. !bhv:ntp4vc_siwl_behavior.
                  ntp4vc_siwl_exec_while
                    (ntp4vc_siwl_mk_loop_cnf n) o3
                    (ntp4vc_siwl_compose
                      (ntp4vc_siwl_rho s3) (ntp4vc_siwl_sigma s3))
                    e c gamma' bhv
                  ==>
                  ?s':(A,B)ntp4vc_siwl_sym_state.
                    ntp4vc_siwl_in_results bhv s' normals1
                      (ntp4vc_siwl_to_set unbounds3)
                      (ntp4vc_siwl_to_set limits3) /\
                    ntp4vc_siwl_is_solution
                      (ntp4vc_siwl_rho s') (ntp4vc_siwl_constr s') /\
                    gamma' =
                    ntp4vc_siwl_compose
                      (ntp4vc_siwl_rho s') (ntp4vc_siwl_sigma s')) /\
             (!bhv:ntp4vc_siwl_behavior.
              !s':(A,B)ntp4vc_siwl_sym_state.
                ntp4vc_siwl_in_results bhv s' normals1
                  (ntp4vc_siwl_to_set unbounds3)
                  (ntp4vc_siwl_to_set limits3)
                ==>
                ntp4vc_siwl_is_solution
                  (ntp4vc_siwl_rho s') (ntp4vc_siwl_constr s')
                ==>
                ?s3:(A,B)ntp4vc_siwl_sym_state.
                  s3 IN ntp4vc_siwl_to_set
                    (NTP4VC_SIWL_SymStateSet o2) /\
                  ntp4vc_siwl_is_solution
                    (ntp4vc_siwl_rho s3) (ntp4vc_siwl_constr s3) /\
                  ntp4vc_siwl_exec_while
                    (ntp4vc_siwl_mk_loop_cnf n) o3
                    (ntp4vc_siwl_compose
                      (ntp4vc_siwl_rho s3) (ntp4vc_siwl_sigma s3))
                    e c
                    (ntp4vc_siwl_compose
                      (ntp4vc_siwl_rho s') (ntp4vc_siwl_sigma s'))
                    bhv) /\
             limits1 =
               ntp4vc_siwl_to_set limits2 UNION
               ntp4vc_siwl_to_set limits3 /\
             unbounds1 =
               ntp4vc_siwl_to_set unbounds2 UNION
               ntp4vc_siwl_to_set unbounds3) \/
        (~flag /\
         ntp4vc_siwl_empty_result limits1 /\
         ntp4vc_siwl_empty_result unbounds1 /\
         ntp4vc_siwl_empty_result normals1))`;;

let ntp4vc_siwl_exit_branch_results = new_definition
  `ntp4vc_siwl_exit_branch_results
     (s2:(A,B)ntp4vc_siwl_sym_state)
     (normals2:(A,B)ntp4vc_siwl_sym_state->bool)
     (unbounds2:(A,B)ntp4vc_siwl_sym_state->bool)
     (limits2:(A,B)ntp4vc_siwl_sym_state->bool) <=>
     ?flag:bool.
       (~flag
        ==> !r:B->int.
              ~ntp4vc_siwl_is_solution r (ntp4vc_siwl_constr s2)) /\
       ((flag /\
         ntp4vc_siwl_empty_result limits2 /\
         ntp4vc_siwl_empty_result unbounds2 /\
         ntp4vc_siwl_single_result normals2 s2) \/
        (~flag /\
         ntp4vc_siwl_empty_result limits2 /\
         ntp4vc_siwl_empty_result unbounds2 /\
         ntp4vc_siwl_empty_result normals2))`;;

let ntp4vc_siwl_while_pre = new_definition
 `ntp4vc_siwl_while_pre
    (ctr:int) (n:int)
    (s:(A,B)ntp4vc_siwl_sym_state)
    (e:A ntp4vc_siwl_expr)
    (c:A ntp4vc_siwl_cmd) <=>
    (~(ctr = n)
      ==>
      !sym_cond:B ntp4vc_siwl_symbolic_expr.
        ntp4vc_siwl_eval_expr
          (ntp4vc_siwl_compose
            (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
          e
          (NTP4VC_SIWL_Enormal
            (ntp4vc_siwl_interp_symbolic_expr
              (ntp4vc_siwl_rho s) sym_cond)) /\
        ntp4vc_siwl_symbolic_expr_supported
          (ntp4vc_siwl_sigma s) sym_cond
        ==>
        let co1 =
          NTP4VC_SIWL_Cconj (ntp4vc_siwl_constr s)
            (NTP4VC_SIWL_Cneq sym_cond (NTP4VC_SIWL_Slit (&0))) in
        ntp4vc_siwl_vars_in_constraint co1
          SUBSET ntp4vc_siwl_vars s /\
        ntp4vc_siwl_store_supported
          (ntp4vc_siwl_sigma s) (ntp4vc_siwl_vars s) /\
        (!s1:(A,B)ntp4vc_siwl_sym_state.
           ntp4vc_siwl_state_has_fields s1
             (ntp4vc_siwl_sigma s) co1
             (ntp4vc_siwl_rho s) (ntp4vc_siwl_vars s)
           ==>
           let co2 =
             NTP4VC_SIWL_Cconj (ntp4vc_siwl_constr s)
               (NTP4VC_SIWL_Ceq sym_cond (NTP4VC_SIWL_Slit (&0))) in
           ntp4vc_siwl_vars_in_constraint co2
             SUBSET ntp4vc_siwl_vars s /\
           ntp4vc_siwl_store_supported
             (ntp4vc_siwl_sigma s) (ntp4vc_siwl_vars s) /\
           (!s2:(A,B)ntp4vc_siwl_sym_state.
              ntp4vc_siwl_state_has_fields s2
                (ntp4vc_siwl_sigma s) co2
                (ntp4vc_siwl_rho s) (ntp4vc_siwl_vars s)
              ==>
              (T = F
               ==> !r:B->int.
                     ~ntp4vc_siwl_is_solution
                       r (ntp4vc_siwl_constr s1))
              ==>
              (&0:int) <= n /\
              (!normals1 unbounds1 limits1:
                  (A,B)ntp4vc_siwl_sym_state_set.
                 ntp4vc_siwl_good_cmd_results n s1 c
                   (ntp4vc_siwl_to_set normals1)
                   (ntp4vc_siwl_to_set unbounds1)
                   (ntp4vc_siwl_to_set limits1)
                 ==>
                 let o7 = ntp4vc_siwl_to_list normals1 in
                 (!x:(A,B)ntp4vc_siwl_sym_state.
                    x IN ntp4vc_siwl_to_set normals1 <=> MEM x o7)
                 ==>
                 let o8 = ctr + (&1:int) in
                 (((&0:int) <= n - ctr /\ n - o8 < n - ctr) \/
                  (n - ctr = n - o8 /\
                   (&0:int) <= (&0:int) /\
                   &(LENGTH o7) < (&0:int))) /\
                 (&0:int) <= o8 /\
                 o8 <= n))))`;;

let ntp4vc_siwl_step_results = new_definition
 `ntp4vc_siwl_step_results
    (n:int) (ctr:int)
    (s:(A,B)ntp4vc_siwl_sym_state)
    (e:A ntp4vc_siwl_expr)
    (c:A ntp4vc_siwl_cmd)
    (normals:(A,B)ntp4vc_siwl_sym_state_set)
    (unbounds:(A,B)ntp4vc_siwl_sym_state_set)
    (limits:(A,B)ntp4vc_siwl_sym_state_set) <=>
        (if ctr = n then
            ntp4vc_siwl_single_result
              (ntp4vc_siwl_to_set limits) s /\
            ntp4vc_siwl_empty_result
              (ntp4vc_siwl_to_set unbounds) /\
            ntp4vc_siwl_empty_result
              (ntp4vc_siwl_to_set normals)
          else
            ((?sym_cond:B ntp4vc_siwl_symbolic_expr.
                ntp4vc_siwl_eval_expr
                  (ntp4vc_siwl_compose
                    (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
                  e
                  (NTP4VC_SIWL_Enormal
                    (ntp4vc_siwl_interp_symbolic_expr
                      (ntp4vc_siwl_rho s) sym_cond)) /\
                ntp4vc_siwl_symbolic_expr_supported
                  (ntp4vc_siwl_sigma s) sym_cond /\
                (?s1:(A,B)ntp4vc_siwl_sym_state.
                   ntp4vc_siwl_state_has_fields s1
                     (ntp4vc_siwl_sigma s)
                     (NTP4VC_SIWL_Cconj
                       (ntp4vc_siwl_constr s)
                       (NTP4VC_SIWL_Cneq sym_cond
                         (NTP4VC_SIWL_Slit (&0))))
                     (ntp4vc_siwl_rho s) (ntp4vc_siwl_vars s) /\
                   (?s2:(A,B)ntp4vc_siwl_sym_state.
                      ntp4vc_siwl_state_has_fields s2
                        (ntp4vc_siwl_sigma s)
                        (NTP4VC_SIWL_Cconj
                          (ntp4vc_siwl_constr s)
                          (NTP4VC_SIWL_Ceq sym_cond
                            (NTP4VC_SIWL_Slit (&0))))
                        (ntp4vc_siwl_rho s) (ntp4vc_siwl_vars s) /\
                      (?normals1 unbounds1 limits1:
                          (A,B)ntp4vc_siwl_sym_state_set.
                         ntp4vc_siwl_body_branch_results
                           n ctr s1 e c
                           (ntp4vc_siwl_to_set normals1)
                           (ntp4vc_siwl_to_set unbounds1)
                           (ntp4vc_siwl_to_set limits1) /\
                         (?normals2 unbounds2 limits2:
                             (A,B)ntp4vc_siwl_sym_state_set.
                            ntp4vc_siwl_exit_branch_results s2
                              (ntp4vc_siwl_to_set normals2)
                              (ntp4vc_siwl_to_set unbounds2)
                              (ntp4vc_siwl_to_set limits2) /\
                            ntp4vc_siwl_to_set limits =
                              ntp4vc_siwl_to_set limits1 UNION
                              ntp4vc_siwl_to_set limits2 /\
                            ntp4vc_siwl_to_set unbounds =
                              ntp4vc_siwl_to_set unbounds1 UNION
                              ntp4vc_siwl_to_set unbounds2 /\
                            ntp4vc_siwl_to_set normals =
                              ntp4vc_siwl_to_set normals1 UNION
                              ntp4vc_siwl_to_set normals2))))) \/
             ntp4vc_siwl_eval_expr
               (ntp4vc_siwl_compose
                 (ntp4vc_siwl_rho s) (ntp4vc_siwl_sigma s))
               e NTP4VC_SIWL_Eunbound_var /\
             ntp4vc_siwl_empty_result
               (ntp4vc_siwl_to_set limits) /\
             ntp4vc_siwl_single_result
               (ntp4vc_siwl_to_set unbounds) s /\
             ntp4vc_siwl_empty_result
               (ntp4vc_siwl_to_set normals)))`;;

let statement =
 `!ctr:int.
  !n:int.
  !s:(A,B)ntp4vc_siwl_sym_state.
  !e:A ntp4vc_siwl_expr.
  !c:A ntp4vc_siwl_cmd.
    ntp4vc_siwl_valid_state s /\
    (&0:int) <= ctr /\
    ctr <= n
    ==>
    ntp4vc_siwl_while_pre ctr n s e c /\
    (!normals unbounds limits:(A,B)ntp4vc_siwl_sym_state_set.
       ntp4vc_siwl_step_results n ctr s e c normals unbounds limits
       ==>
       ntp4vc_siwl_good_while_results n ctr s e c
         (ntp4vc_siwl_to_set normals)
         (ntp4vc_siwl_to_set unbounds)
         (ntp4vc_siwl_to_set limits))`;;
