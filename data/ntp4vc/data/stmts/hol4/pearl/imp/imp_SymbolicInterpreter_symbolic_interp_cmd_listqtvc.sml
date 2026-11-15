(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmd_listqtvc: a
  verification condition for symbolic interpretation of a list of symbolic
  states, preserving state extension and soundness and completeness with
  respect to the concrete command semantics. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory listTheory pred_setTheory;

Datatype:
  'var imp_si_expr =
    ImpSiElit int
  | ImpSiEvar 'var
  | ImpSiEsub ('var imp_si_expr) ('var imp_si_expr)
End

Datatype:
  'var imp_si_cmd =
    ImpSiCskip
  | ImpSiCassign 'var ('var imp_si_expr)
  | ImpSiCseq ('var imp_si_cmd) ('var imp_si_cmd)
  | ImpSiCif ('var imp_si_expr) ('var imp_si_cmd) ('var imp_si_cmd)
  | ImpSiCwhile ('var imp_si_expr) ('var imp_si_cmd)
End

Datatype:
  imp_si_expr_behaviour =
    ImpSiEnormal int
  | ImpSiEunboundVar
End

Datatype:
  imp_si_behaviour =
    ImpSiCnormal
  | ImpSiCunboundVar
  | ImpSiCloopLimit
End

val imp_si_eval_expr_def = Define `
  (imp_si_eval_expr env (ImpSiElit n) = ImpSiEnormal n) /\
  (imp_si_eval_expr env (ImpSiEvar x) =
     case env x of
       NONE => ImpSiEunboundVar
     | SOME n => ImpSiEnormal n) /\
  (imp_si_eval_expr env (ImpSiEsub e1 e2) =
     case imp_si_eval_expr env e1 of
       ImpSiEunboundVar => ImpSiEunboundVar
     | ImpSiEnormal n1 =>
         case imp_si_eval_expr env e2 of
           ImpSiEunboundVar => ImpSiEunboundVar
         | ImpSiEnormal n2 => ImpSiEnormal (n1 - n2))`;

val _ = Hol_reln `
  (!limit env.
     imp_si_exec_cmd
       limit env ImpSiCskip env ImpSiCnormal) /\
  (!limit env e n v.
     imp_si_eval_expr env e = ImpSiEnormal n ==>
     imp_si_exec_cmd
       limit env (ImpSiCassign v e)
       (\x. if x = v then SOME n else env x)
       ImpSiCnormal) /\
  (!limit env e v.
     imp_si_eval_expr env e = ImpSiEunboundVar ==>
     imp_si_exec_cmd
       limit env (ImpSiCassign v e) env ImpSiCunboundVar) /\
  (!limit env1 c1 env2 c2 env3 bhv.
     imp_si_exec_cmd limit env1 c1 env2 ImpSiCnormal /\
     imp_si_exec_cmd limit env2 c2 env3 bhv ==>
     imp_si_exec_cmd
       limit env1 (ImpSiCseq c1 c2) env3 bhv) /\
  (!limit env1 c1 env2 bhv c2.
     imp_si_exec_cmd limit env1 c1 env2 bhv /\
     bhv <> ImpSiCnormal ==>
     imp_si_exec_cmd
       limit env1 (ImpSiCseq c1 c2) env2 bhv) /\
  (!limit env e c1 c2 env' bhv.
     imp_si_eval_expr env e = ImpSiEnormal (0 : int) /\
     imp_si_exec_cmd limit env c2 env' bhv ==>
     imp_si_exec_cmd
       limit env (ImpSiCif e c1 c2) env' bhv) /\
  (!limit env e n c1 c2 env' bhv.
     n <> (0 : int) /\
     imp_si_eval_expr env e = ImpSiEnormal n /\
     imp_si_exec_cmd limit env c1 env' bhv ==>
     imp_si_exec_cmd
       limit env (ImpSiCif e c1 c2) env' bhv) /\
  (!limit env e c1 c2.
     imp_si_eval_expr env e = ImpSiEunboundVar ==>
     imp_si_exec_cmd
       limit env (ImpSiCif e c1 c2) env ImpSiCunboundVar) /\
  (!limit env e c env' bhv.
     imp_si_exec_while
       limit (0 : int) env e c env' bhv ==>
     imp_si_exec_cmd
       limit env (ImpSiCwhile e c) env' bhv) /\
  (!limit ctr env e c.
     (case limit of
        NONE => F
      | SOME n => n <= ctr) ==>
     imp_si_exec_while
       limit ctr env e c env ImpSiCloopLimit) /\
  (!limit ctr env e c.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_si_eval_expr env e = ImpSiEnormal (0 : int) ==>
     imp_si_exec_while
       limit ctr env e c env ImpSiCnormal) /\
  (!limit ctr env e c.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_si_eval_expr env e = ImpSiEunboundVar ==>
     imp_si_exec_while
       limit ctr env e c env ImpSiCunboundVar) /\
  (!limit ctr env1 e v c env2 bhv.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_si_eval_expr env1 e = ImpSiEnormal v /\
     v <> (0 : int) /\
     imp_si_exec_cmd limit env1 c env2 bhv /\
     bhv <> ImpSiCnormal ==>
     imp_si_exec_while
       limit ctr env1 e c env2 bhv) /\
  (!limit ctr env1 e v c env2 env3 bhv.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_si_eval_expr env1 e = ImpSiEnormal v /\
     v <> (0 : int) /\
     imp_si_exec_cmd limit env1 c env2 ImpSiCnormal /\
     imp_si_exec_while
       limit (ctr + (1 : int)) env2 e c env3 bhv ==>
     imp_si_exec_while
       limit ctr env1 e c env3 bhv)
`;

Datatype:
  'svar imp_si_symbolic_expr =
    ImpSiSlit int
  | ImpSiSvar 'svar
  | ImpSiSsub
      ('svar imp_si_symbolic_expr)
      ('svar imp_si_symbolic_expr)
End

Datatype:
  'svar imp_si_constr =
    ImpSiCtrue
  | ImpSiCfalse
  | ImpSiCeq
      ('svar imp_si_symbolic_expr)
      ('svar imp_si_symbolic_expr)
  | ImpSiCneq
      ('svar imp_si_symbolic_expr)
      ('svar imp_si_symbolic_expr)
  | ImpSiCconj ('svar imp_si_constr) ('svar imp_si_constr)
  | ImpSiCexists 'svar ('svar imp_si_constr)
End

val imp_si_interp_symbolic_expr_def = Define `
  (imp_si_interp_symbolic_expr rho (ImpSiSlit n) = n) /\
  (imp_si_interp_symbolic_expr rho (ImpSiSvar v) = rho v) /\
  (imp_si_interp_symbolic_expr rho (ImpSiSsub e1 e2) =
     imp_si_interp_symbolic_expr rho e1 -
     imp_si_interp_symbolic_expr rho e2)`;

val imp_si_is_solution_def = Define `
  (imp_si_is_solution rho ImpSiCtrue = T) /\
  (imp_si_is_solution rho ImpSiCfalse = F) /\
  (imp_si_is_solution rho (ImpSiCeq e1 e2) =
     (imp_si_interp_symbolic_expr rho e1 =
      imp_si_interp_symbolic_expr rho e2)) /\
  (imp_si_is_solution rho (ImpSiCneq e1 e2) =
     (imp_si_interp_symbolic_expr rho e1 <>
      imp_si_interp_symbolic_expr rho e2)) /\
  (imp_si_is_solution rho (ImpSiCconj c1 c2) =
     (imp_si_is_solution rho c1 /\
      imp_si_is_solution rho c2)) /\
  (imp_si_is_solution rho (ImpSiCexists v c) =
     imp_si_is_solution rho c)`;

val imp_si_vars_in_symbolic_expr_def = Define `
  (imp_si_vars_in_symbolic_expr (ImpSiSlit n) = {}) /\
  (imp_si_vars_in_symbolic_expr (ImpSiSvar v) = {v}) /\
  (imp_si_vars_in_symbolic_expr (ImpSiSsub e1 e2) =
     imp_si_vars_in_symbolic_expr e1 UNION
     imp_si_vars_in_symbolic_expr e2)`;

val imp_si_vars_in_constraint_def = Define `
  (imp_si_vars_in_constraint ImpSiCtrue = {}) /\
  (imp_si_vars_in_constraint ImpSiCfalse = {}) /\
  (imp_si_vars_in_constraint (ImpSiCeq e1 e2) =
     imp_si_vars_in_symbolic_expr e1 UNION
     imp_si_vars_in_symbolic_expr e2) /\
  (imp_si_vars_in_constraint (ImpSiCneq e1 e2) =
     imp_si_vars_in_symbolic_expr e1 UNION
     imp_si_vars_in_symbolic_expr e2) /\
  (imp_si_vars_in_constraint (ImpSiCconj c1 c2) =
     imp_si_vars_in_constraint c1 UNION
     imp_si_vars_in_constraint c2) /\
  (imp_si_vars_in_constraint (ImpSiCexists v c) =
     v INSERT imp_si_vars_in_constraint c)`;

val imp_si_compose_def = Define `
  imp_si_compose get rho sigma x =
    case get sigma x of
      NONE => NONE
    | SOME v => SOME (rho v)`;

val imp_si_state_extends_def = Define `
  imp_si_state_extends to_var_set vars rho s s' <=>
    to_var_set (vars s) SUBSET to_var_set (vars s') /\
    !v.
      v IN to_var_set (vars s) ==>
      rho s v = rho s' v`;

val imp_si_results_extend_def = Define `
  imp_si_results_extend to_var_set vars rho
      s normals unbounds limits <=>
    !s'.
      s' IN normals \/ s' IN unbounds \/ s' IN limits ==>
      imp_si_state_extends to_var_set vars rho s s'`;

val imp_si_in_result_def = Define `
  imp_si_in_result bhv s normals unbounds limits <=>
    case bhv of
      ImpSiCnormal => s IN normals
    | ImpSiCunboundVar => s IN unbounds
    | ImpSiCloopLimit => s IN limits`;

val imp_si_head_spec_def = Define `
  imp_si_head_spec get sigma constr rho to_var_set vars n c
      s normals unbounds limits <=>
    imp_si_results_extend to_var_set vars rho
      s normals unbounds limits /\
    (imp_si_is_solution (rho s) (constr s) ==>
     !gamma' bhv.
       imp_si_exec_cmd
         (SOME n)
         (imp_si_compose get (rho s) (sigma s))
         c gamma' bhv ==>
       ?s'.
         imp_si_in_result
           bhv s' normals unbounds limits /\
         imp_si_is_solution (rho s') (constr s') /\
         gamma' =
           imp_si_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_si_in_result
         bhv s' normals unbounds limits ==>
       imp_si_is_solution (rho s') (constr s') ==>
       imp_si_is_solution (rho s) (constr s) /\
       imp_si_exec_cmd
         (SOME n)
         (imp_si_compose get (rho s) (sigma s))
         c
         (imp_si_compose get (rho s') (sigma s'))
         bhv)`;

val imp_si_list_spec_def = Define `
  imp_si_list_spec get sigma constr rho to_var_set vars n c
      ss normals unbounds limits <=>
    (!s'.
       s' IN normals \/ s' IN unbounds \/ s' IN limits ==>
       ?s.
         s IN set ss /\
         imp_si_state_extends to_var_set vars rho s s') /\
    (!s.
       s IN set ss ==>
       imp_si_is_solution (rho s) (constr s) ==>
       !gamma' bhv.
         imp_si_exec_cmd
           (SOME n)
           (imp_si_compose get (rho s) (sigma s))
           c gamma' bhv ==>
         ?s'.
           imp_si_in_result
             bhv s' normals unbounds limits /\
           imp_si_is_solution (rho s') (constr s') /\
           gamma' =
             imp_si_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_si_in_result
         bhv s' normals unbounds limits ==>
       imp_si_is_solution (rho s') (constr s') ==>
       ?s.
         s IN set ss /\
         imp_si_is_solution (rho s) (constr s) /\
         imp_si_exec_cmd
           (SOME n)
           (imp_si_compose get (rho s) (sigma s))
           c
           (imp_si_compose get (rho s') (sigma s'))
           bhv)`;

val imp_SymbolicInterpreter_symbolic_interp_cmd_list_vc =
  ``!(get : 'sigma -> 'var -> 'svar option)
      (sigma : 'state -> 'sigma)
      (constr : 'state -> 'svar imp_si_constr)
      (rho : 'state -> 'svar -> int)
      (to_var_set : 'varset -> 'svar set)
      (vars : 'state -> 'varset)
      (n : int)
      (ss : 'state list)
      (c : 'var imp_si_cmd).
      (!vs. FINITE (to_var_set vs)) /\
      (!s.
         FINITE s ==>
         ?vs. to_var_set vs = s) /\
      (!s.
         imp_si_vars_in_constraint (constr s) SUBSET
           to_var_set (vars s) /\
         (!x v.
            get (sigma s) x = SOME v ==>
            v IN to_var_set (vars s))) /\
      (!a b.
         sigma a = sigma b /\
         constr a = constr b /\
         rho a = rho b /\
         vars a = vars b ==>
         a = b) /\
      (!sig con vs r.
         imp_si_vars_in_constraint con SUBSET
           to_var_set vs /\
         (!x v.
            get sig x = SOME v ==>
            v IN to_var_set vs) ==>
         ?s.
           sigma s = sig /\
           constr s = con /\
           vars s = vs /\
           rho s = r) /\
      (0 : int) <= n
      ==>
      (case ss of
         [] => T
       | s :: ss' =>
           (((0 : int) <= &(LENGTH ss) /\
             (0 : int) < &(LENGTH ss)) /\
            (0 : int) <= n) /\
           !normals1 unbounds1 limits1.
             FINITE normals1 /\
             FINITE unbounds1 /\
             FINITE limits1 /\
             imp_si_head_spec
               get sigma constr rho to_var_set vars n c
               s normals1 unbounds1 limits1
             ==>
             (((0 : int) <= &(LENGTH ss) /\
               LENGTH ss' < LENGTH ss) /\
              (0 : int) <= n)) /\
      !normals unbounds limits.
        FINITE normals /\
        FINITE unbounds /\
        FINITE limits
        ==>
        ((case ss of
            [] =>
              (limits = {} /\ &(CARD limits) = (0 : int)) /\
              (unbounds = {} /\
               &(CARD unbounds) = (0 : int)) /\
              normals = {} /\
              &(CARD normals) = (0 : int)
          | s :: ss' =>
              ?normals1 unbounds1 limits1.
                FINITE normals1 /\
                FINITE unbounds1 /\
                FINITE limits1 /\
                imp_si_head_spec
                  get sigma constr rho to_var_set vars n c
                  s normals1 unbounds1 limits1 /\
                ?normals2 unbounds2 limits2.
                  FINITE normals2 /\
                  FINITE unbounds2 /\
                  FINITE limits2 /\
                  imp_si_list_spec
                    get sigma constr rho to_var_set vars n c
                    ss' normals2 unbounds2 limits2 /\
                  limits = limits1 UNION limits2 /\
                  unbounds = unbounds1 UNION unbounds2 /\
                  normals = normals1 UNION normals2)
         ==>
         imp_si_list_spec
           get sigma constr rho to_var_set vars n c
           ss normals unbounds limits)``;
