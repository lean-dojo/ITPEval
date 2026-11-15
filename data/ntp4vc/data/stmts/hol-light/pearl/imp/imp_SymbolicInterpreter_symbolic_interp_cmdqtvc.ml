(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmdqtvc: the verification
  condition for one-step symbolic interpretation of bounded IMP commands,
  including assignments, sequencing, conditionals, loops, and error outcomes.
  This file contains no proof.
*)

let ntp4vc_sicl_expr_INDUCT,ntp4vc_sicl_expr_RECURSION = define_type
  "ntp4vc_sicl_expr =
       NTP4VC_SICL_Elit int
     | NTP4VC_SICL_Evar A
     | NTP4VC_SICL_Esub ntp4vc_sicl_expr ntp4vc_sicl_expr";;

let ntp4vc_sicl_cmd_INDUCT,ntp4vc_sicl_cmd_RECURSION = define_type
  "ntp4vc_sicl_cmd =
       NTP4VC_SICL_Cskip
     | NTP4VC_SICL_Cassign A (A ntp4vc_sicl_expr)
     | NTP4VC_SICL_Cseq ntp4vc_sicl_cmd ntp4vc_sicl_cmd
     | NTP4VC_SICL_Cif
         (A ntp4vc_sicl_expr) ntp4vc_sicl_cmd ntp4vc_sicl_cmd
     | NTP4VC_SICL_Cwhile (A ntp4vc_sicl_expr) ntp4vc_sicl_cmd";;

let ntp4vc_sicl_expr_behavior_INDUCT,
    ntp4vc_sicl_expr_behavior_RECURSION = define_type
  "ntp4vc_sicl_expr_behavior =
       NTP4VC_SICL_Enormal int
     | NTP4VC_SICL_Eunbound_var";;

let ntp4vc_sicl_behavior_INDUCT,ntp4vc_sicl_behavior_RECURSION = define_type
  "ntp4vc_sicl_behavior =
       NTP4VC_SICL_Cnormal
     | NTP4VC_SICL_Cunbound_var
     | NTP4VC_SICL_Cloop_limit";;

let ntp4vc_sicl_config_INDUCT,ntp4vc_sicl_config_RECURSION = define_type
  "ntp4vc_sicl_config =
       NTP4VC_SICL_No_limit
     | NTP4VC_SICL_Loop_limit num";;

let ntp4vc_sicl_mk_loop_cnf = new_definition
  `ntp4vc_sicl_mk_loop_cnf (n:int) =
     NTP4VC_SICL_Loop_limit (num_of_int n)`;;

let ntp4vc_sicl_under_limit =
  new_recursive_definition ntp4vc_sicl_config_RECURSION
   `(!ctr:int.
       ntp4vc_sicl_under_limit NTP4VC_SICL_No_limit ctr <=> T) /\
    (!n:num. !ctr:int.
       ntp4vc_sicl_under_limit (NTP4VC_SICL_Loop_limit n) ctr <=>
       ctr < &n)`;;

let ntp4vc_sicl_at_limit =
  new_recursive_definition ntp4vc_sicl_config_RECURSION
   `(!ctr:int.
       ntp4vc_sicl_at_limit NTP4VC_SICL_No_limit ctr <=> F) /\
    (!n:num. !ctr:int.
       ntp4vc_sicl_at_limit (NTP4VC_SICL_Loop_limit n) ctr <=>
       &n <= ctr)`;;

let ntp4vc_sicl_update = new_definition
  `ntp4vc_sicl_update (env:A->int option) (v:A) (n:int) =
     \x. if x = v then SOME n else env x`;;

let ntp4vc_sicl_eval_expr_RULES,
    ntp4vc_sicl_eval_expr_INDUCT,
    ntp4vc_sicl_eval_expr_CASES =
  new_inductive_definition
   `(!env:A->int option. !n:int.
       ntp4vc_sicl_eval_expr
         env (NTP4VC_SICL_Elit n) (NTP4VC_SICL_Enormal n)) /\
    (!env:A->int option. !x:A. !n:int.
       env x = SOME n
       ==> ntp4vc_sicl_eval_expr
             env (NTP4VC_SICL_Evar x) (NTP4VC_SICL_Enormal n)) /\
    (!env:A->int option. !x:A.
       env x = NONE
       ==> ntp4vc_sicl_eval_expr
             env (NTP4VC_SICL_Evar x) NTP4VC_SICL_Eunbound_var) /\
    (!env:A->int option. !e1 e2:A ntp4vc_sicl_expr. !n1 n2:int.
       ntp4vc_sicl_eval_expr env e1 (NTP4VC_SICL_Enormal n1) /\
       ntp4vc_sicl_eval_expr env e2 (NTP4VC_SICL_Enormal n2)
       ==> ntp4vc_sicl_eval_expr
             env (NTP4VC_SICL_Esub e1 e2)
             (NTP4VC_SICL_Enormal (n1 - n2))) /\
    (!env:A->int option. !e1 e2:A ntp4vc_sicl_expr.
       ntp4vc_sicl_eval_expr env e1 NTP4VC_SICL_Eunbound_var
       ==> ntp4vc_sicl_eval_expr
             env (NTP4VC_SICL_Esub e1 e2)
             NTP4VC_SICL_Eunbound_var) /\
    (!env:A->int option. !e1 e2:A ntp4vc_sicl_expr. !n1:int.
       ntp4vc_sicl_eval_expr env e1 (NTP4VC_SICL_Enormal n1) /\
       ntp4vc_sicl_eval_expr env e2 NTP4VC_SICL_Eunbound_var
       ==> ntp4vc_sicl_eval_expr
             env (NTP4VC_SICL_Esub e1 e2)
             NTP4VC_SICL_Eunbound_var)`;;

let ntp4vc_sicl_exec_RULES,
    ntp4vc_sicl_exec_INDUCT,
    ntp4vc_sicl_exec_CASES =
  new_inductive_definition
   `(!cnf:ntp4vc_sicl_config. !env:A->int option.
       ntp4vc_sicl_exec_cmd
         cnf env NTP4VC_SICL_Cskip env NTP4VC_SICL_Cnormal) /\
    (!cnf:ntp4vc_sicl_config. !env:A->int option.
     !v:A. !e:A ntp4vc_sicl_expr. !n:int.
       ntp4vc_sicl_eval_expr env e (NTP4VC_SICL_Enormal n)
       ==> ntp4vc_sicl_exec_cmd cnf env
             (NTP4VC_SICL_Cassign v e)
             (ntp4vc_sicl_update env v n)
             NTP4VC_SICL_Cnormal) /\
    (!cnf:ntp4vc_sicl_config. !env:A->int option.
     !v:A. !e:A ntp4vc_sicl_expr.
       ntp4vc_sicl_eval_expr env e NTP4VC_SICL_Eunbound_var
       ==> ntp4vc_sicl_exec_cmd cnf env
             (NTP4VC_SICL_Cassign v e) env NTP4VC_SICL_Cunbound_var) /\
    (!cnf:ntp4vc_sicl_config.
     !env1 env2 env3:A->int option.
     !c1 c2:A ntp4vc_sicl_cmd. !bhv:ntp4vc_sicl_behavior.
       ntp4vc_sicl_exec_cmd cnf env1 c1 env2 NTP4VC_SICL_Cnormal /\
       ntp4vc_sicl_exec_cmd cnf env2 c2 env3 bhv
       ==> ntp4vc_sicl_exec_cmd
             cnf env1 (NTP4VC_SICL_Cseq c1 c2) env3 bhv) /\
    (!cnf:ntp4vc_sicl_config. !env1 env2:A->int option.
     !c1 c2:A ntp4vc_sicl_cmd. !bhv:ntp4vc_sicl_behavior.
       ntp4vc_sicl_exec_cmd cnf env1 c1 env2 bhv /\
       ~(bhv = NTP4VC_SICL_Cnormal)
       ==> ntp4vc_sicl_exec_cmd
             cnf env1 (NTP4VC_SICL_Cseq c1 c2) env2 bhv) /\
    (!cnf:ntp4vc_sicl_config. !env env':A->int option.
     !e:A ntp4vc_sicl_expr. !c1 c2:A ntp4vc_sicl_cmd.
     !bhv:ntp4vc_sicl_behavior.
       ntp4vc_sicl_eval_expr env e (NTP4VC_SICL_Enormal (&0)) /\
       ntp4vc_sicl_exec_cmd cnf env c2 env' bhv
       ==> ntp4vc_sicl_exec_cmd
             cnf env (NTP4VC_SICL_Cif e c1 c2) env' bhv) /\
    (!cnf:ntp4vc_sicl_config. !env env':A->int option.
     !e:A ntp4vc_sicl_expr. !c1 c2:A ntp4vc_sicl_cmd.
     !n:int. !bhv:ntp4vc_sicl_behavior.
       ~(n = &0) /\
       ntp4vc_sicl_eval_expr env e (NTP4VC_SICL_Enormal n) /\
       ntp4vc_sicl_exec_cmd cnf env c1 env' bhv
       ==> ntp4vc_sicl_exec_cmd
             cnf env (NTP4VC_SICL_Cif e c1 c2) env' bhv) /\
    (!cnf:ntp4vc_sicl_config. !env:A->int option.
     !e:A ntp4vc_sicl_expr. !c1 c2:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_eval_expr env e NTP4VC_SICL_Eunbound_var
       ==> ntp4vc_sicl_exec_cmd cnf env
             (NTP4VC_SICL_Cif e c1 c2)
             env NTP4VC_SICL_Cunbound_var) /\
    (!cnf:ntp4vc_sicl_config. !env env':A->int option.
     !e:A ntp4vc_sicl_expr. !c:A ntp4vc_sicl_cmd.
     !bhv:ntp4vc_sicl_behavior.
       ntp4vc_sicl_exec_while cnf (&0) env e c env' bhv
       ==> ntp4vc_sicl_exec_cmd
             cnf env (NTP4VC_SICL_Cwhile e c) env' bhv) /\
    (!cnf:ntp4vc_sicl_config. !ctr:int. !env:A->int option.
     !e:A ntp4vc_sicl_expr. !c:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_at_limit cnf ctr
       ==> ntp4vc_sicl_exec_while
             cnf ctr env e c env NTP4VC_SICL_Cloop_limit) /\
    (!cnf:ntp4vc_sicl_config. !ctr:int. !env:A->int option.
     !e:A ntp4vc_sicl_expr. !c:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_under_limit cnf ctr /\
       ntp4vc_sicl_eval_expr env e (NTP4VC_SICL_Enormal (&0))
       ==> ntp4vc_sicl_exec_while
             cnf ctr env e c env NTP4VC_SICL_Cnormal) /\
    (!cnf:ntp4vc_sicl_config. !ctr:int. !env:A->int option.
     !e:A ntp4vc_sicl_expr. !c:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_under_limit cnf ctr /\
       ntp4vc_sicl_eval_expr env e NTP4VC_SICL_Eunbound_var
       ==> ntp4vc_sicl_exec_while
             cnf ctr env e c env NTP4VC_SICL_Cunbound_var) /\
    (!cnf:ntp4vc_sicl_config. !ctr:int.
     !env1 env2:A->int option.
     !e:A ntp4vc_sicl_expr. !c:A ntp4vc_sicl_cmd.
     !v:int. !bhv:ntp4vc_sicl_behavior.
       ntp4vc_sicl_under_limit cnf ctr /\
       ntp4vc_sicl_eval_expr env1 e (NTP4VC_SICL_Enormal v) /\
       ~(v = &0) /\
       ntp4vc_sicl_exec_cmd cnf env1 c env2 bhv /\
       ~(bhv = NTP4VC_SICL_Cnormal)
       ==> ntp4vc_sicl_exec_while cnf ctr env1 e c env2 bhv) /\
    (!cnf:ntp4vc_sicl_config. !ctr:int.
     !env1 env2 env3:A->int option.
     !e:A ntp4vc_sicl_expr. !c:A ntp4vc_sicl_cmd.
     !v:int. !bhv:ntp4vc_sicl_behavior.
       ntp4vc_sicl_under_limit cnf ctr /\
       ntp4vc_sicl_eval_expr env1 e (NTP4VC_SICL_Enormal v) /\
       ~(v = &0) /\
       ntp4vc_sicl_exec_cmd cnf env1 c env2 NTP4VC_SICL_Cnormal /\
       ntp4vc_sicl_exec_while cnf (ctr + &1) env2 e c env3 bhv
       ==> ntp4vc_sicl_exec_while cnf ctr env1 e c env3 bhv)`;;

let ntp4vc_sicl_symbolic_expr_INDUCT,
    ntp4vc_sicl_symbolic_expr_RECURSION = define_type
  "ntp4vc_sicl_symbolic_expr =
       NTP4VC_SICL_Slit int
     | NTP4VC_SICL_Svar B
     | NTP4VC_SICL_Ssub
         ntp4vc_sicl_symbolic_expr ntp4vc_sicl_symbolic_expr";;

let ntp4vc_sicl_constr_INDUCT,ntp4vc_sicl_constr_RECURSION = define_type
  "ntp4vc_sicl_constr =
       NTP4VC_SICL_Ctrue
     | NTP4VC_SICL_Cfalse
     | NTP4VC_SICL_Ceq
         (B ntp4vc_sicl_symbolic_expr)
         (B ntp4vc_sicl_symbolic_expr)
     | NTP4VC_SICL_Cneq
         (B ntp4vc_sicl_symbolic_expr)
         (B ntp4vc_sicl_symbolic_expr)
     | NTP4VC_SICL_Cconj ntp4vc_sicl_constr ntp4vc_sicl_constr
     | NTP4VC_SICL_Cexists B ntp4vc_sicl_constr";;

let ntp4vc_sicl_interp_symbolic_expr =
  new_recursive_definition ntp4vc_sicl_symbolic_expr_RECURSION
   `(!rho:B->int. !n:int.
       ntp4vc_sicl_interp_symbolic_expr rho (NTP4VC_SICL_Slit n) = n) /\
    (!rho:B->int. !v:B.
       ntp4vc_sicl_interp_symbolic_expr rho (NTP4VC_SICL_Svar v) =
       rho v) /\
    (!rho:B->int. !e1 e2:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_interp_symbolic_expr rho (NTP4VC_SICL_Ssub e1 e2) =
       ntp4vc_sicl_interp_symbolic_expr rho e1 -
       ntp4vc_sicl_interp_symbolic_expr rho e2)`;;

let ntp4vc_sicl_is_solution =
  new_recursive_definition ntp4vc_sicl_constr_RECURSION
   `(!rho:B->int.
       ntp4vc_sicl_is_solution rho NTP4VC_SICL_Ctrue <=> T) /\
    (!rho:B->int.
       ntp4vc_sicl_is_solution rho NTP4VC_SICL_Cfalse <=> F) /\
    (!rho:B->int. !e1 e2:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_is_solution rho (NTP4VC_SICL_Ceq e1 e2) <=>
       ntp4vc_sicl_interp_symbolic_expr rho e1 =
       ntp4vc_sicl_interp_symbolic_expr rho e2) /\
    (!rho:B->int. !e1 e2:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_is_solution rho (NTP4VC_SICL_Cneq e1 e2) <=>
       ~(ntp4vc_sicl_interp_symbolic_expr rho e1 =
         ntp4vc_sicl_interp_symbolic_expr rho e2)) /\
    (!rho:B->int. !c1 c2:B ntp4vc_sicl_constr.
       ntp4vc_sicl_is_solution rho (NTP4VC_SICL_Cconj c1 c2) <=>
       ntp4vc_sicl_is_solution rho c1 /\
       ntp4vc_sicl_is_solution rho c2) /\
    (!rho:B->int. !v:B. !c:B ntp4vc_sicl_constr.
       ntp4vc_sicl_is_solution rho (NTP4VC_SICL_Cexists v c) <=>
       ntp4vc_sicl_is_solution rho c)`;;

let ntp4vc_sicl_vars_in_symbolic_expr =
  new_recursive_definition ntp4vc_sicl_symbolic_expr_RECURSION
   `(!n:int.
       ntp4vc_sicl_vars_in_symbolic_expr (NTP4VC_SICL_Slit n) =
       ({}:B->bool)) /\
    (!v:B.
       ntp4vc_sicl_vars_in_symbolic_expr (NTP4VC_SICL_Svar v) = {v}) /\
    (!e1 e2:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_vars_in_symbolic_expr (NTP4VC_SICL_Ssub e1 e2) =
       ntp4vc_sicl_vars_in_symbolic_expr e1 UNION
       ntp4vc_sicl_vars_in_symbolic_expr e2)`;;

let ntp4vc_sicl_vars_in_constraint =
  new_recursive_definition ntp4vc_sicl_constr_RECURSION
   `(ntp4vc_sicl_vars_in_constraint NTP4VC_SICL_Ctrue =
      ({}:B->bool)) /\
    (ntp4vc_sicl_vars_in_constraint NTP4VC_SICL_Cfalse =
      ({}:B->bool)) /\
    (!e1 e2:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_vars_in_constraint (NTP4VC_SICL_Ceq e1 e2) =
       ntp4vc_sicl_vars_in_symbolic_expr e1 UNION
       ntp4vc_sicl_vars_in_symbolic_expr e2) /\
    (!e1 e2:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_vars_in_constraint (NTP4VC_SICL_Cneq e1 e2) =
       ntp4vc_sicl_vars_in_symbolic_expr e1 UNION
       ntp4vc_sicl_vars_in_symbolic_expr e2) /\
    (!c1 c2:B ntp4vc_sicl_constr.
       ntp4vc_sicl_vars_in_constraint (NTP4VC_SICL_Cconj c1 c2) =
       ntp4vc_sicl_vars_in_constraint c1 UNION
       ntp4vc_sicl_vars_in_constraint c2) /\
    (!v:B. !c:B ntp4vc_sicl_constr.
       ntp4vc_sicl_vars_in_constraint (NTP4VC_SICL_Cexists v c) =
       v INSERT ntp4vc_sicl_vars_in_constraint c)`;;

let ntp4vc_sicl_sym_state_INDUCT,ntp4vc_sicl_sym_state_RECURSION =
  define_type
   "ntp4vc_sicl_sym_state =
      NTP4VC_SICL_SymState
        (A->B option) (B ntp4vc_sicl_constr) (B->int) (B->bool)";;

let ntp4vc_sicl_sigma =
  new_recursive_definition ntp4vc_sicl_sym_state_RECURSION
   `ntp4vc_sicl_sigma (NTP4VC_SICL_SymState sg co r vs) = sg`;;

let ntp4vc_sicl_constr =
  new_recursive_definition ntp4vc_sicl_sym_state_RECURSION
   `ntp4vc_sicl_constr (NTP4VC_SICL_SymState sg co r vs) = co`;;

let ntp4vc_sicl_rho =
  new_recursive_definition ntp4vc_sicl_sym_state_RECURSION
   `ntp4vc_sicl_rho (NTP4VC_SICL_SymState sg co r vs) = r`;;

let ntp4vc_sicl_vars =
  new_recursive_definition ntp4vc_sicl_sym_state_RECURSION
   `ntp4vc_sicl_vars (NTP4VC_SICL_SymState sg co r vs) = vs`;;

let ntp4vc_sicl_valid_state = new_definition
  `ntp4vc_sicl_valid_state (s:(A,B)ntp4vc_sicl_sym_state) <=>
     FINITE (ntp4vc_sicl_vars s) /\
     ntp4vc_sicl_vars_in_constraint (ntp4vc_sicl_constr s)
       SUBSET ntp4vc_sicl_vars s /\
     (!x:A. !v:B.
        ntp4vc_sicl_sigma s x = SOME v
        ==> v IN ntp4vc_sicl_vars s)`;;

let ntp4vc_sicl_sym_state_set_INDUCT,
    ntp4vc_sicl_sym_state_set_RECURSION = define_type
  "ntp4vc_sicl_sym_state_set =
     NTP4VC_SICL_SymStateSet ((A,B)ntp4vc_sicl_sym_state)list";;

let ntp4vc_sicl_to_set =
  new_recursive_definition ntp4vc_sicl_sym_state_set_RECURSION
   `ntp4vc_sicl_to_set (NTP4VC_SICL_SymStateSet xs) =
      {s | ntp4vc_sicl_valid_state s /\ MEM s xs}`;;

let ntp4vc_sicl_apply_option =
  new_recursive_definition option_RECURSION
   `(!r:B->int.
       ntp4vc_sicl_apply_option r NONE = NONE) /\
    (!r:B->int. !v:B.
       ntp4vc_sicl_apply_option r (SOME v) = SOME (r v))`;;

let ntp4vc_sicl_compose = new_definition
  `ntp4vc_sicl_compose (r:B->int) (sg:A->B option) (x:A) =
     ntp4vc_sicl_apply_option r (sg x)`;;

let ntp4vc_sicl_state_extends = new_definition
  `ntp4vc_sicl_state_extends
     (s:(A,B)ntp4vc_sicl_sym_state)
     (s':(A,B)ntp4vc_sicl_sym_state) <=>
     ntp4vc_sicl_vars s SUBSET ntp4vc_sicl_vars s' /\
     (!v:B.
        v IN ntp4vc_sicl_vars s
        ==> ntp4vc_sicl_rho s v = ntp4vc_sicl_rho s' v)`;;

let ntp4vc_sicl_results_extend = new_definition
  `ntp4vc_sicl_results_extend
     (s:(A,B)ntp4vc_sicl_sym_state)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     !s':(A,B)ntp4vc_sicl_sym_state.
       s' IN normals \/ s' IN unbounds \/ s' IN limits
       ==> ntp4vc_sicl_state_extends s s'`;;

let ntp4vc_sicl_in_results = new_definition
  `ntp4vc_sicl_in_results
     (bhv:ntp4vc_sicl_behavior)
     (s:(A,B)ntp4vc_sicl_sym_state)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     (bhv = NTP4VC_SICL_Cnormal /\ s IN normals) \/
     (bhv = NTP4VC_SICL_Cunbound_var /\ s IN unbounds) \/
     (bhv = NTP4VC_SICL_Cloop_limit /\ s IN limits)`;;

let ntp4vc_sicl_to_list =
  new_recursive_definition ntp4vc_sicl_sym_state_set_RECURSION
   `ntp4vc_sicl_to_list (NTP4VC_SICL_SymStateSet xs) =
      FILTER ntp4vc_sicl_valid_state xs`;;

let ntp4vc_sicl_sigma_update = new_definition
  `ntp4vc_sicl_sigma_update (sg:A->B option) (x:A) (v:B) =
     \k. if k = x then SOME v else sg k`;;

let ntp4vc_sicl_rho_update = new_definition
  `ntp4vc_sicl_rho_update (r:B->int) (v:B) (z:int) =
     \w. if w = v then z else r w`;;

let ntp4vc_sicl_symbolic_expr_supported = new_definition
  `ntp4vc_sicl_symbolic_expr_supported
     (sg:A->B option) (se:B ntp4vc_sicl_symbolic_expr) <=>
     !v:B.
       v IN ntp4vc_sicl_vars_in_symbolic_expr se
       ==> ?x:A. sg x = SOME v`;;

let ntp4vc_sicl_store_supported = new_definition
  `ntp4vc_sicl_store_supported (sg:A->B option) (vs:B->bool) <=>
     !x:A. !v:B. sg x = SOME v ==> v IN vs`;;

let ntp4vc_sicl_state_has_fields = new_definition
  `ntp4vc_sicl_state_has_fields
     (s:(A,B)ntp4vc_sicl_sym_state)
     (sg:A->B option)
     (co:B ntp4vc_sicl_constr)
     (r:B->int)
     (vs:B->bool) <=>
     ntp4vc_sicl_valid_state s /\
     ntp4vc_sicl_sigma s = sg /\
     ntp4vc_sicl_constr s = co /\
     ntp4vc_sicl_rho s = r /\
     ntp4vc_sicl_vars s = vs`;;

let ntp4vc_sicl_empty_result = new_definition
  `ntp4vc_sicl_empty_result
     (xs:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     xs = {} /\ &(CARD xs) = (&0:int)`;;

let ntp4vc_sicl_single_result = new_definition
  `ntp4vc_sicl_single_result
     (xs:(A,B)ntp4vc_sicl_sym_state->bool)
     (s:(A,B)ntp4vc_sicl_sym_state) <=>
     xs = {s} /\ &(CARD xs) = (&1:int)`;;

let ntp4vc_sicl_direct_subcommand =
  new_recursive_definition ntp4vc_sicl_cmd_RECURSION
   `(!d:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_direct_subcommand NTP4VC_SICL_Cskip d <=> F) /\
    (!x:A. !e:A ntp4vc_sicl_expr. !d:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_direct_subcommand (NTP4VC_SICL_Cassign x e) d <=>
       F) /\
    (!c1 c2 d:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_direct_subcommand (NTP4VC_SICL_Cseq c1 c2) d <=>
       c1 = d \/ c2 = d) /\
    (!e:A ntp4vc_sicl_expr. !c1 c2 d:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_direct_subcommand (NTP4VC_SICL_Cif e c1 c2) d <=>
       c1 = d \/ c2 = d) /\
    (!e:A ntp4vc_sicl_expr. !c d:A ntp4vc_sicl_cmd.
       ntp4vc_sicl_direct_subcommand (NTP4VC_SICL_Cwhile e c) d <=>
       c = d)`;;

let ntp4vc_sicl_good_cmd_results = new_definition
  `ntp4vc_sicl_good_cmd_results
     (n:int)
     (s:(A,B)ntp4vc_sicl_sym_state)
     (c:A ntp4vc_sicl_cmd)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     ntp4vc_sicl_results_extend s normals unbounds limits /\
     (ntp4vc_sicl_is_solution
        (ntp4vc_sicl_rho s) (ntp4vc_sicl_constr s)
      ==>
      !gamma':A->int option. !bhv:ntp4vc_sicl_behavior.
        ntp4vc_sicl_exec_cmd (ntp4vc_sicl_mk_loop_cnf n)
          (ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
          c gamma' bhv
        ==>
        ?s':(A,B)ntp4vc_sicl_sym_state.
          ntp4vc_sicl_in_results bhv s' normals unbounds limits /\
          ntp4vc_sicl_is_solution
            (ntp4vc_sicl_rho s') (ntp4vc_sicl_constr s') /\
          gamma' =
          ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s') (ntp4vc_sicl_sigma s')) /\
     (!bhv:ntp4vc_sicl_behavior.
      !s':(A,B)ntp4vc_sicl_sym_state.
        ntp4vc_sicl_in_results bhv s' normals unbounds limits
        ==>
        ntp4vc_sicl_is_solution
          (ntp4vc_sicl_rho s') (ntp4vc_sicl_constr s')
        ==>
        ntp4vc_sicl_is_solution
          (ntp4vc_sicl_rho s) (ntp4vc_sicl_constr s) /\
        ntp4vc_sicl_exec_cmd (ntp4vc_sicl_mk_loop_cnf n)
          (ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
          c
          (ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s') (ntp4vc_sicl_sigma s'))
          bhv)`;;

let ntp4vc_sicl_good_while_results = new_definition
  `ntp4vc_sicl_good_while_results
     (n:int)
     (s:(A,B)ntp4vc_sicl_sym_state)
     (e:A ntp4vc_sicl_expr)
     (c:A ntp4vc_sicl_cmd)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     ntp4vc_sicl_results_extend s normals unbounds limits /\
     (ntp4vc_sicl_is_solution
        (ntp4vc_sicl_rho s) (ntp4vc_sicl_constr s)
      ==>
      !gamma':A->int option. !bhv:ntp4vc_sicl_behavior.
        ntp4vc_sicl_exec_while (ntp4vc_sicl_mk_loop_cnf n) (&0)
          (ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
          e c gamma' bhv
        ==>
        ?s':(A,B)ntp4vc_sicl_sym_state.
          ntp4vc_sicl_in_results bhv s' normals unbounds limits /\
          ntp4vc_sicl_is_solution
            (ntp4vc_sicl_rho s') (ntp4vc_sicl_constr s') /\
          gamma' =
          ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s') (ntp4vc_sicl_sigma s')) /\
     (!bhv:ntp4vc_sicl_behavior.
      !s':(A,B)ntp4vc_sicl_sym_state.
        ntp4vc_sicl_in_results bhv s' normals unbounds limits
        ==>
        ntp4vc_sicl_is_solution
          (ntp4vc_sicl_rho s') (ntp4vc_sicl_constr s')
        ==>
        ntp4vc_sicl_is_solution
          (ntp4vc_sicl_rho s) (ntp4vc_sicl_constr s) /\
        ntp4vc_sicl_exec_while (ntp4vc_sicl_mk_loop_cnf n) (&0)
          (ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
          e c
          (ntp4vc_sicl_compose
            (ntp4vc_sicl_rho s') (ntp4vc_sicl_sigma s'))
          bhv)`;;

let ntp4vc_sicl_assignment_constraint = new_definition
  `ntp4vc_sicl_assignment_constraint
     (s:(A,B)ntp4vc_sicl_sym_state)
     (x:A) (v':B)
     (se:B ntp4vc_sicl_symbolic_expr)
     (constr':B ntp4vc_sicl_constr) <=>
     let constr =
       NTP4VC_SICL_Cconj (ntp4vc_sicl_constr s)
         (NTP4VC_SICL_Ceq (NTP4VC_SICL_Svar v') se) in
     ((?v:B.
         ntp4vc_sicl_sigma s x = SOME v /\
         (!r:B->int.
            ntp4vc_sicl_is_solution r constr' <=>
            ntp4vc_sicl_is_solution r (NTP4VC_SICL_Cexists v constr)) /\
         ntp4vc_sicl_vars_in_constraint constr'
           SUBSET
         ntp4vc_sicl_vars_in_constraint
           (NTP4VC_SICL_Cexists v constr)) \/
      ntp4vc_sicl_sigma s x = NONE /\ constr' = constr)`;;

let ntp4vc_sicl_added_vars = new_definition
  `ntp4vc_sicl_added_vars
     (old:B->bool) (v:B) (fresh:B->bool) <=>
     fresh = v INSERT old /\
     (if v IN old
      then CARD fresh = CARD old
      else &(CARD fresh) = &(CARD old) + (&1:int))`;;

let ntp4vc_sicl_assignment_wf = new_definition
  `ntp4vc_sicl_assignment_wf
     (s:(A,B)ntp4vc_sicl_sym_state)
     (x:A) (e:A ntp4vc_sicl_expr) <=>
     !se:B ntp4vc_sicl_symbolic_expr.
       ntp4vc_sicl_eval_expr
         (ntp4vc_sicl_compose
           (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
         e
         (NTP4VC_SICL_Enormal
           (ntp4vc_sicl_interp_symbolic_expr
             (ntp4vc_sicl_rho s) se)) /\
       ntp4vc_sicl_symbolic_expr_supported
         (ntp4vc_sicl_sigma s) se
       ==>
       !v':B.
         ~(v' IN ntp4vc_sicl_vars s)
         ==>
         let sigma' =
           ntp4vc_sicl_sigma_update (ntp4vc_sicl_sigma s) x v' in
         sigma' x = SOME v' /\
         (!k':A. ~(k' = x) ==> sigma' k' = ntp4vc_sicl_sigma s k')
         ==>
         !constr':B ntp4vc_sicl_constr.
           ntp4vc_sicl_assignment_constraint s x v' se constr'
           ==>
           !vars':B->bool.
             ntp4vc_sicl_added_vars (ntp4vc_sicl_vars s) v' vars'
             ==>
             ntp4vc_sicl_vars_in_constraint constr' SUBSET vars' /\
             ntp4vc_sicl_store_supported sigma' vars'`;;

let ntp4vc_sicl_assignment_results = new_definition
  `ntp4vc_sicl_assignment_results
     (s:(A,B)ntp4vc_sicl_sym_state)
     (x:A) (e:A ntp4vc_sicl_expr)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     ((?se:B ntp4vc_sicl_symbolic_expr.
         ntp4vc_sicl_eval_expr
           (ntp4vc_sicl_compose
             (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
           e
           (NTP4VC_SICL_Enormal
             (ntp4vc_sicl_interp_symbolic_expr
               (ntp4vc_sicl_rho s) se)) /\
         ntp4vc_sicl_symbolic_expr_supported
           (ntp4vc_sicl_sigma s) se /\
         (?v':B.
            ~(v' IN ntp4vc_sicl_vars s) /\
            let sigma' =
              ntp4vc_sicl_sigma_update (ntp4vc_sicl_sigma s) x v' in
            (sigma' x = SOME v' /\
             (!k':A.
                ~(k' = x) ==> sigma' k' = ntp4vc_sicl_sigma s k')) /\
            (?constr':B ntp4vc_sicl_constr.
               ntp4vc_sicl_assignment_constraint s x v' se constr' /\
               (?vars':B->bool.
                  ntp4vc_sicl_added_vars
                    (ntp4vc_sicl_vars s) v' vars' /\
                  (?s':(A,B)ntp4vc_sicl_sym_state.
                     ntp4vc_sicl_state_has_fields s'
                       sigma' constr'
                       (ntp4vc_sicl_rho_update
                         (ntp4vc_sicl_rho s) v'
                         (ntp4vc_sicl_interp_symbolic_expr
                           (ntp4vc_sicl_rho s) se))
                       vars' /\
                     ntp4vc_sicl_empty_result limits /\
                     ntp4vc_sicl_empty_result unbounds /\
                     ntp4vc_sicl_single_result normals s'))))) \/
      ntp4vc_sicl_eval_expr
        (ntp4vc_sicl_compose
          (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
        e NTP4VC_SICL_Eunbound_var /\
      ntp4vc_sicl_empty_result limits /\
      ntp4vc_sicl_single_result unbounds s /\
      ntp4vc_sicl_empty_result normals)`;;

let ntp4vc_sicl_branch_results = new_definition
  `ntp4vc_sicl_branch_results
     (n:int)
     (s:(A,B)ntp4vc_sicl_sym_state)
     (c:A ntp4vc_sicl_cmd)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     ?flag:bool.
       (~flag
        ==> (!r:B->int.
               ~ntp4vc_sicl_is_solution r (ntp4vc_sicl_constr s))) /\
       ((flag /\
         ntp4vc_sicl_good_cmd_results
           n s c normals unbounds limits) \/
        (~flag /\
         ntp4vc_sicl_empty_result limits /\
         ntp4vc_sicl_empty_result unbounds /\
         ntp4vc_sicl_empty_result normals))`;;

let ntp4vc_sicl_sequence_results = new_definition
  `ntp4vc_sicl_sequence_results
     (n:int)
     (s:(A,B)ntp4vc_sicl_sym_state)
     (c1:A ntp4vc_sicl_cmd)
     (c2:A ntp4vc_sicl_cmd)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     ?normals1 unbounds1 limits1:
        (A,B)ntp4vc_sicl_sym_state_set.
       ntp4vc_sicl_good_cmd_results n s c1
         (ntp4vc_sicl_to_set normals1)
         (ntp4vc_sicl_to_set unbounds1)
         (ntp4vc_sicl_to_set limits1) /\
       let o1 = ntp4vc_sicl_to_list normals1 in
       (!e:(A,B)ntp4vc_sicl_sym_state.
          e IN ntp4vc_sicl_to_set normals1 <=> MEM e o1) /\
       (?unbounds2 limits2:(A,B)ntp4vc_sicl_sym_state_set.
          (!s':(A,B)ntp4vc_sicl_sym_state.
             s' IN normals \/
             s' IN ntp4vc_sicl_to_set unbounds2 \/
             s' IN ntp4vc_sicl_to_set limits2
             ==>
             ?s1:(A,B)ntp4vc_sicl_sym_state.
               s1 IN ntp4vc_sicl_to_set
                 (NTP4VC_SICL_SymStateSet o1) /\
               ntp4vc_sicl_state_extends s1 s') /\
          (!s1:(A,B)ntp4vc_sicl_sym_state.
             s1 IN ntp4vc_sicl_to_set
               (NTP4VC_SICL_SymStateSet o1)
             ==>
             ntp4vc_sicl_is_solution
               (ntp4vc_sicl_rho s1) (ntp4vc_sicl_constr s1)
             ==>
             !gamma':A->int option. !bhv:ntp4vc_sicl_behavior.
               ntp4vc_sicl_exec_cmd (ntp4vc_sicl_mk_loop_cnf n)
                 (ntp4vc_sicl_compose
                   (ntp4vc_sicl_rho s1) (ntp4vc_sicl_sigma s1))
                 c2 gamma' bhv
               ==>
               ?s':(A,B)ntp4vc_sicl_sym_state.
                 ntp4vc_sicl_in_results bhv s' normals
                   (ntp4vc_sicl_to_set unbounds2)
                   (ntp4vc_sicl_to_set limits2) /\
                 ntp4vc_sicl_is_solution
                   (ntp4vc_sicl_rho s') (ntp4vc_sicl_constr s') /\
                 gamma' =
                 ntp4vc_sicl_compose
                   (ntp4vc_sicl_rho s') (ntp4vc_sicl_sigma s')) /\
          (!bhv:ntp4vc_sicl_behavior.
           !s':(A,B)ntp4vc_sicl_sym_state.
             ntp4vc_sicl_in_results bhv s' normals
               (ntp4vc_sicl_to_set unbounds2)
               (ntp4vc_sicl_to_set limits2)
             ==>
             ntp4vc_sicl_is_solution
               (ntp4vc_sicl_rho s') (ntp4vc_sicl_constr s')
             ==>
             ?s1:(A,B)ntp4vc_sicl_sym_state.
               s1 IN ntp4vc_sicl_to_set
                 (NTP4VC_SICL_SymStateSet o1) /\
               ntp4vc_sicl_is_solution
                 (ntp4vc_sicl_rho s1) (ntp4vc_sicl_constr s1) /\
               ntp4vc_sicl_exec_cmd (ntp4vc_sicl_mk_loop_cnf n)
                 (ntp4vc_sicl_compose
                   (ntp4vc_sicl_rho s1) (ntp4vc_sicl_sigma s1))
                 c2
                 (ntp4vc_sicl_compose
                   (ntp4vc_sicl_rho s') (ntp4vc_sicl_sigma s'))
                 bhv) /\
          limits =
            ntp4vc_sicl_to_set limits1 UNION
            ntp4vc_sicl_to_set limits2 /\
          unbounds =
            ntp4vc_sicl_to_set unbounds1 UNION
            ntp4vc_sicl_to_set unbounds2)`;;

let ntp4vc_sicl_conditional_results = new_definition
  `ntp4vc_sicl_conditional_results
     (n:int)
     (s:(A,B)ntp4vc_sicl_sym_state)
     (e:A ntp4vc_sicl_expr)
     (c1:A ntp4vc_sicl_cmd)
     (c2:A ntp4vc_sicl_cmd)
     (normals:(A,B)ntp4vc_sicl_sym_state->bool)
     (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
     (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
     ((?se:B ntp4vc_sicl_symbolic_expr.
         ntp4vc_sicl_eval_expr
           (ntp4vc_sicl_compose
             (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
           e
           (NTP4VC_SICL_Enormal
             (ntp4vc_sicl_interp_symbolic_expr
               (ntp4vc_sicl_rho s) se)) /\
         ntp4vc_sicl_symbolic_expr_supported
           (ntp4vc_sicl_sigma s) se /\
         (?s1:(A,B)ntp4vc_sicl_sym_state.
            ntp4vc_sicl_state_has_fields s1
              (ntp4vc_sicl_sigma s)
              (NTP4VC_SICL_Cconj (ntp4vc_sicl_constr s)
                (NTP4VC_SICL_Cneq se (NTP4VC_SICL_Slit (&0))))
              (ntp4vc_sicl_rho s) (ntp4vc_sicl_vars s) /\
            (?s2:(A,B)ntp4vc_sicl_sym_state.
               ntp4vc_sicl_state_has_fields s2
                 (ntp4vc_sicl_sigma s)
                 (NTP4VC_SICL_Cconj (ntp4vc_sicl_constr s)
                   (NTP4VC_SICL_Ceq se (NTP4VC_SICL_Slit (&0))))
                 (ntp4vc_sicl_rho s) (ntp4vc_sicl_vars s) /\
               (?normals1 unbounds1 limits1:
                   (A,B)ntp4vc_sicl_sym_state_set.
                  ntp4vc_sicl_branch_results n s1 c1
                    (ntp4vc_sicl_to_set normals1)
                    (ntp4vc_sicl_to_set unbounds1)
                    (ntp4vc_sicl_to_set limits1) /\
                  (?normals2 unbounds2 limits2:
                      (A,B)ntp4vc_sicl_sym_state_set.
                     ntp4vc_sicl_branch_results n s2 c2
                       (ntp4vc_sicl_to_set normals2)
                       (ntp4vc_sicl_to_set unbounds2)
                       (ntp4vc_sicl_to_set limits2) /\
                     limits =
                       ntp4vc_sicl_to_set limits1 UNION
                       ntp4vc_sicl_to_set limits2 /\
                     unbounds =
                       ntp4vc_sicl_to_set unbounds1 UNION
                       ntp4vc_sicl_to_set unbounds2 /\
                     normals =
                       ntp4vc_sicl_to_set normals1 UNION
                       ntp4vc_sicl_to_set normals2))))) \/
      ntp4vc_sicl_eval_expr
        (ntp4vc_sicl_compose
          (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
        e NTP4VC_SICL_Eunbound_var /\
      ntp4vc_sicl_empty_result limits /\
      ntp4vc_sicl_single_result unbounds s /\
      ntp4vc_sicl_empty_result normals)`;;

let ntp4vc_sicl_sequence_pre = new_definition
 `ntp4vc_sicl_sequence_pre
    (n:int) (s:(A,B)ntp4vc_sicl_sym_state)
    (c1:A ntp4vc_sicl_cmd) (c2:A ntp4vc_sicl_cmd) <=>
    (ntp4vc_sicl_direct_subcommand
       (NTP4VC_SICL_Cseq c1 c2) c1 /\
     (&0:int) <= n) /\
    (!normals1 unbounds1 limits1:
        (A,B)ntp4vc_sicl_sym_state_set.
       ntp4vc_sicl_good_cmd_results n s c1
         (ntp4vc_sicl_to_set normals1)
         (ntp4vc_sicl_to_set unbounds1)
         (ntp4vc_sicl_to_set limits1)
       ==>
       let o1 = ntp4vc_sicl_to_list normals1 in
       (!e:(A,B)ntp4vc_sicl_sym_state.
          e IN ntp4vc_sicl_to_set normals1 <=> MEM e o1)
       ==>
       (ntp4vc_sicl_direct_subcommand
          (NTP4VC_SICL_Cseq c1 c2) c2 \/
        NTP4VC_SICL_Cseq c1 c2 = c2 /\
        (&0:int) <= (&0:int) /\
        &(LENGTH o1) < (&0:int)) /\
       (&0:int) <= n)`;;

let ntp4vc_sicl_conditional_pre = new_definition
 `ntp4vc_sicl_conditional_pre
    (n:int) (s:(A,B)ntp4vc_sicl_sym_state)
    (e:A ntp4vc_sicl_expr)
    (c1:A ntp4vc_sicl_cmd) (c2:A ntp4vc_sicl_cmd) <=>
    !se:B ntp4vc_sicl_symbolic_expr.
      ntp4vc_sicl_eval_expr
        (ntp4vc_sicl_compose
          (ntp4vc_sicl_rho s) (ntp4vc_sicl_sigma s))
        e
        (NTP4VC_SICL_Enormal
          (ntp4vc_sicl_interp_symbolic_expr
            (ntp4vc_sicl_rho s) se)) /\
      ntp4vc_sicl_symbolic_expr_supported
        (ntp4vc_sicl_sigma s) se
      ==>
      let co1 =
        NTP4VC_SICL_Cconj (ntp4vc_sicl_constr s)
          (NTP4VC_SICL_Cneq se (NTP4VC_SICL_Slit (&0))) in
      ntp4vc_sicl_vars_in_constraint co1
        SUBSET ntp4vc_sicl_vars s /\
      ntp4vc_sicl_store_supported
        (ntp4vc_sicl_sigma s) (ntp4vc_sicl_vars s) /\
      (!s1:(A,B)ntp4vc_sicl_sym_state.
         ntp4vc_sicl_state_has_fields s1
           (ntp4vc_sicl_sigma s) co1
           (ntp4vc_sicl_rho s) (ntp4vc_sicl_vars s)
         ==>
         let co2 =
           NTP4VC_SICL_Cconj (ntp4vc_sicl_constr s)
             (NTP4VC_SICL_Ceq se (NTP4VC_SICL_Slit (&0))) in
         ntp4vc_sicl_vars_in_constraint co2
           SUBSET ntp4vc_sicl_vars s /\
         ntp4vc_sicl_store_supported
           (ntp4vc_sicl_sigma s) (ntp4vc_sicl_vars s) /\
         (!s2:(A,B)ntp4vc_sicl_sym_state.
            ntp4vc_sicl_state_has_fields s2
              (ntp4vc_sicl_sigma s) co2
              (ntp4vc_sicl_rho s) (ntp4vc_sicl_vars s)
            ==>
            (((T = F
               ==> !r:B->int.
                     ~ntp4vc_sicl_is_solution
                       r (ntp4vc_sicl_constr s1))
              ==>
              ntp4vc_sicl_direct_subcommand
                (NTP4VC_SICL_Cif e c1 c2) c1 /\
              (&0:int) <= n) /\
             (!normals1 unbounds1 limits1:
                 (A,B)ntp4vc_sicl_sym_state_set.
                ntp4vc_sicl_branch_results n s1 c1
                  (ntp4vc_sicl_to_set normals1)
                  (ntp4vc_sicl_to_set unbounds1)
                  (ntp4vc_sicl_to_set limits1)
                ==>
                (T = F
                 ==> !r:B->int.
                       ~ntp4vc_sicl_is_solution
                         r (ntp4vc_sicl_constr s2))
                ==>
                ntp4vc_sicl_direct_subcommand
                  (NTP4VC_SICL_Cif e c1 c2) c2 /\
                (&0:int) <= n))))`;;

let ntp4vc_sicl_while_pre = new_definition
 `ntp4vc_sicl_while_pre
    (n:int) (e:A ntp4vc_sicl_expr) (c:A ntp4vc_sicl_cmd) <=>
    (ntp4vc_sicl_direct_subcommand
       (NTP4VC_SICL_Cwhile e c) (NTP4VC_SICL_Cwhile e c) \/
     NTP4VC_SICL_Cwhile e c = NTP4VC_SICL_Cwhile e c /\
     (&0:int) <= n + (&1:int) /\
     n - (&0:int) < n + (&1:int)) /\
    (&0:int) <= (&0:int) /\
    (&0:int) <= n`;;

let ntp4vc_sicl_pre = new_definition
 `ntp4vc_sicl_pre
    (n:int) (s:(A,B)ntp4vc_sicl_sym_state) (c:A ntp4vc_sicl_cmd) <=>
    c = NTP4VC_SICL_Cskip \/
    (?x:A. ?e:A ntp4vc_sicl_expr.
       c = NTP4VC_SICL_Cassign x e /\
       ntp4vc_sicl_assignment_wf s x e) \/
    (?c1:A ntp4vc_sicl_cmd. ?c2:A ntp4vc_sicl_cmd.
       c = NTP4VC_SICL_Cseq c1 c2 /\
       ntp4vc_sicl_sequence_pre n s c1 c2) \/
    (?e:A ntp4vc_sicl_expr.
     ?c1:A ntp4vc_sicl_cmd. ?c2:A ntp4vc_sicl_cmd.
       c = NTP4VC_SICL_Cif e c1 c2 /\
       ntp4vc_sicl_conditional_pre n s e c1 c2) \/
    (?e:A ntp4vc_sicl_expr. ?body:A ntp4vc_sicl_cmd.
       c = NTP4VC_SICL_Cwhile e body /\
       ntp4vc_sicl_while_pre n e body)`;;

let ntp4vc_sicl_step_results = new_definition
 `ntp4vc_sicl_step_results
    (n:int) (s:(A,B)ntp4vc_sicl_sym_state) (c:A ntp4vc_sicl_cmd)
    (normals:(A,B)ntp4vc_sicl_sym_state->bool)
    (unbounds:(A,B)ntp4vc_sicl_sym_state->bool)
    (limits:(A,B)ntp4vc_sicl_sym_state->bool) <=>
    (c = NTP4VC_SICL_Cskip /\
     ntp4vc_sicl_empty_result limits /\
     ntp4vc_sicl_empty_result unbounds /\
     ntp4vc_sicl_single_result normals s) \/
    (?x:A. ?e:A ntp4vc_sicl_expr.
       c = NTP4VC_SICL_Cassign x e /\
       ntp4vc_sicl_assignment_results
         s x e normals unbounds limits) \/
    (?c1:A ntp4vc_sicl_cmd. ?c2:A ntp4vc_sicl_cmd.
       c = NTP4VC_SICL_Cseq c1 c2 /\
       ntp4vc_sicl_sequence_results
         n s c1 c2 normals unbounds limits) \/
    (?e:A ntp4vc_sicl_expr.
     ?c1:A ntp4vc_sicl_cmd. ?c2:A ntp4vc_sicl_cmd.
       c = NTP4VC_SICL_Cif e c1 c2 /\
       ntp4vc_sicl_conditional_results
         n s e c1 c2 normals unbounds limits) \/
    (?e:A ntp4vc_sicl_expr. ?body:A ntp4vc_sicl_cmd.
       c = NTP4VC_SICL_Cwhile e body /\
       ntp4vc_sicl_good_while_results
         n s e body normals unbounds limits)`;;

let statement =
 `!n:int.
  !c:A ntp4vc_sicl_cmd.
  !s:(A,B)ntp4vc_sicl_sym_state.
    ntp4vc_sicl_valid_state s /\
    (&0:int) <= n
    ==>
    ntp4vc_sicl_pre n s c /\
    (!normals unbounds limits:(A,B)ntp4vc_sicl_sym_state_set.
       ntp4vc_sicl_step_results n s c
         (ntp4vc_sicl_to_set normals)
         (ntp4vc_sicl_to_set unbounds)
         (ntp4vc_sicl_to_set limits)
       ==>
       ntp4vc_sicl_good_cmd_results n s c
         (ntp4vc_sicl_to_set normals)
         (ntp4vc_sicl_to_set unbounds)
         (ntp4vc_sicl_to_set limits))`;;
