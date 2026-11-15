(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_while_listqtvc: a
  verification condition for symbolic interpretation of a list of symbolic
  states through bounded while-loop execution, preserving state extension and
  soundness and completeness. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory listTheory pred_setTheory;

Datatype:
  imp_siwl_expr =
    ImpSiwlElit int
  | ImpSiwlEvar 'a
  | ImpSiwlEsub imp_siwl_expr imp_siwl_expr
End

Datatype:
  imp_siwl_cmd =
    ImpSiwlCskip
  | ImpSiwlCassign 'a ('a imp_siwl_expr)
  | ImpSiwlCseq imp_siwl_cmd imp_siwl_cmd
  | ImpSiwlCif
      ('a imp_siwl_expr)
      imp_siwl_cmd
      imp_siwl_cmd
  | ImpSiwlCwhile ('a imp_siwl_expr) imp_siwl_cmd
End

Datatype:
  imp_siwl_expr_behaviour =
    ImpSiwlEnormal int
  | ImpSiwlEunboundVar
End

Datatype:
  imp_siwl_behaviour =
    ImpSiwlCnormal
  | ImpSiwlCunboundVar
  | ImpSiwlCloopLimit
End

val imp_siwl_eval_expr_def = Define `
  (imp_siwl_eval_expr env (ImpSiwlElit n) = ImpSiwlEnormal n) /\
  (imp_siwl_eval_expr env (ImpSiwlEvar x) =
     case env x of
       NONE => ImpSiwlEunboundVar
     | SOME n => ImpSiwlEnormal n) /\
  (imp_siwl_eval_expr env (ImpSiwlEsub e1 e2) =
     case imp_siwl_eval_expr env e1 of
       ImpSiwlEunboundVar => ImpSiwlEunboundVar
     | ImpSiwlEnormal n1 =>
         case imp_siwl_eval_expr env e2 of
           ImpSiwlEunboundVar => ImpSiwlEunboundVar
         | ImpSiwlEnormal n2 => ImpSiwlEnormal (n1 - n2))`;

val _ = Hol_reln `
  (!limit env.
     imp_siwl_exec_cmd
       limit env ImpSiwlCskip env ImpSiwlCnormal) /\
  (!limit env e n v.
     imp_siwl_eval_expr env e = ImpSiwlEnormal n ==>
     imp_siwl_exec_cmd
       limit env (ImpSiwlCassign v e)
       (\x. if x = v then SOME n else env x)
       ImpSiwlCnormal) /\
  (!limit env e v.
     imp_siwl_eval_expr env e = ImpSiwlEunboundVar ==>
     imp_siwl_exec_cmd
       limit env (ImpSiwlCassign v e) env ImpSiwlCunboundVar) /\
  (!limit env1 c1 env2 c2 env3 bhv.
     imp_siwl_exec_cmd limit env1 c1 env2 ImpSiwlCnormal /\
     imp_siwl_exec_cmd limit env2 c2 env3 bhv ==>
     imp_siwl_exec_cmd
       limit env1 (ImpSiwlCseq c1 c2) env3 bhv) /\
  (!limit env1 c1 env2 bhv c2.
     imp_siwl_exec_cmd limit env1 c1 env2 bhv /\
     bhv <> ImpSiwlCnormal ==>
     imp_siwl_exec_cmd
       limit env1 (ImpSiwlCseq c1 c2) env2 bhv) /\
  (!limit env e c1 c2 env' bhv.
     imp_siwl_eval_expr env e = ImpSiwlEnormal (0 : int) /\
     imp_siwl_exec_cmd limit env c2 env' bhv ==>
     imp_siwl_exec_cmd
       limit env (ImpSiwlCif e c1 c2) env' bhv) /\
  (!limit env e n c1 c2 env' bhv.
     n <> (0 : int) /\
     imp_siwl_eval_expr env e = ImpSiwlEnormal n /\
     imp_siwl_exec_cmd limit env c1 env' bhv ==>
     imp_siwl_exec_cmd
       limit env (ImpSiwlCif e c1 c2) env' bhv) /\
  (!limit env e c1 c2.
     imp_siwl_eval_expr env e = ImpSiwlEunboundVar ==>
     imp_siwl_exec_cmd
       limit env (ImpSiwlCif e c1 c2) env ImpSiwlCunboundVar) /\
  (!limit env e c env' bhv.
     imp_siwl_exec_while
       limit (0 : int) env e c env' bhv ==>
     imp_siwl_exec_cmd
       limit env (ImpSiwlCwhile e c) env' bhv) /\
  (!limit ctr env e c.
     (case limit of
        NONE => F
      | SOME n => n <= ctr) ==>
     imp_siwl_exec_while
       limit ctr env e c env ImpSiwlCloopLimit) /\
  (!limit ctr env e c.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siwl_eval_expr env e = ImpSiwlEnormal (0 : int) ==>
     imp_siwl_exec_while
       limit ctr env e c env ImpSiwlCnormal) /\
  (!limit ctr env e c.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siwl_eval_expr env e = ImpSiwlEunboundVar ==>
     imp_siwl_exec_while
       limit ctr env e c env ImpSiwlCunboundVar) /\
  (!limit ctr env1 e v c env2 bhv.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siwl_eval_expr env1 e = ImpSiwlEnormal v /\
     v <> (0 : int) /\
     imp_siwl_exec_cmd limit env1 c env2 bhv /\
     bhv <> ImpSiwlCnormal ==>
     imp_siwl_exec_while
       limit ctr env1 e c env2 bhv) /\
  (!limit ctr env1 e v c env2 env3 bhv.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siwl_eval_expr env1 e = ImpSiwlEnormal v /\
     v <> (0 : int) /\
     imp_siwl_exec_cmd limit env1 c env2 ImpSiwlCnormal /\
     imp_siwl_exec_while
       limit (ctr + (1 : int)) env2 e c env3 bhv ==>
     imp_siwl_exec_while
       limit ctr env1 e c env3 bhv)
`;

Datatype:
  imp_siwl_symbolic_expr =
    ImpSiwlSlit int
  | ImpSiwlSvar 'a
  | ImpSiwlSsub
      imp_siwl_symbolic_expr
      imp_siwl_symbolic_expr
End

Datatype:
  imp_siwl_constr =
    ImpSiwlCtrue
  | ImpSiwlCfalse
  | ImpSiwlCeq
      ('a imp_siwl_symbolic_expr)
      ('a imp_siwl_symbolic_expr)
  | ImpSiwlCneq
      ('a imp_siwl_symbolic_expr)
      ('a imp_siwl_symbolic_expr)
  | ImpSiwlCconj
      imp_siwl_constr
      imp_siwl_constr
  | ImpSiwlCexists 'a imp_siwl_constr
End

val imp_siwl_interp_symbolic_expr_def = Define `
  (imp_siwl_interp_symbolic_expr rho (ImpSiwlSlit n) = n) /\
  (imp_siwl_interp_symbolic_expr rho (ImpSiwlSvar v) = rho v) /\
  (imp_siwl_interp_symbolic_expr rho (ImpSiwlSsub e1 e2) =
     imp_siwl_interp_symbolic_expr rho e1 -
     imp_siwl_interp_symbolic_expr rho e2)`;

val imp_siwl_is_solution_def = Define `
  (imp_siwl_is_solution rho ImpSiwlCtrue = T) /\
  (imp_siwl_is_solution rho ImpSiwlCfalse = F) /\
  (imp_siwl_is_solution rho (ImpSiwlCeq e1 e2) =
     (imp_siwl_interp_symbolic_expr rho e1 =
      imp_siwl_interp_symbolic_expr rho e2)) /\
  (imp_siwl_is_solution rho (ImpSiwlCneq e1 e2) =
     (imp_siwl_interp_symbolic_expr rho e1 <>
      imp_siwl_interp_symbolic_expr rho e2)) /\
  (imp_siwl_is_solution rho (ImpSiwlCconj c1 c2) =
     (imp_siwl_is_solution rho c1 /\
      imp_siwl_is_solution rho c2)) /\
  (imp_siwl_is_solution rho (ImpSiwlCexists v c) =
     imp_siwl_is_solution rho c)`;

val imp_siwl_vars_in_symbolic_expr_def = Define `
  (imp_siwl_vars_in_symbolic_expr (ImpSiwlSlit n) = {}) /\
  (imp_siwl_vars_in_symbolic_expr (ImpSiwlSvar v) = {v}) /\
  (imp_siwl_vars_in_symbolic_expr (ImpSiwlSsub e1 e2) =
     imp_siwl_vars_in_symbolic_expr e1 UNION
     imp_siwl_vars_in_symbolic_expr e2)`;

val imp_siwl_vars_in_constraint_def = Define `
  (imp_siwl_vars_in_constraint ImpSiwlCtrue = {}) /\
  (imp_siwl_vars_in_constraint ImpSiwlCfalse = {}) /\
  (imp_siwl_vars_in_constraint (ImpSiwlCeq e1 e2) =
     imp_siwl_vars_in_symbolic_expr e1 UNION
     imp_siwl_vars_in_symbolic_expr e2) /\
  (imp_siwl_vars_in_constraint (ImpSiwlCneq e1 e2) =
     imp_siwl_vars_in_symbolic_expr e1 UNION
     imp_siwl_vars_in_symbolic_expr e2) /\
  (imp_siwl_vars_in_constraint (ImpSiwlCconj c1 c2) =
     imp_siwl_vars_in_constraint c1 UNION
     imp_siwl_vars_in_constraint c2) /\
  (imp_siwl_vars_in_constraint (ImpSiwlCexists v c) =
     v INSERT imp_siwl_vars_in_constraint c)`;

val imp_siwl_compose_def = Define `
  imp_siwl_compose get rho sigma x =
    case get sigma x of
      NONE => NONE
    | SOME v => SOME (rho v)`;

val imp_siwl_state_extends_def = Define `
  imp_siwl_state_extends to_var_set vars rho s s' <=>
    to_var_set (vars s) SUBSET to_var_set (vars s') /\
    !v.
      v IN to_var_set (vars s) ==>
      rho s v = rho s' v`;

val imp_siwl_results_extend_def = Define `
  imp_siwl_results_extend to_var_set vars rho
      s normals unbounds limits <=>
    !s'.
      s' IN normals \/ s' IN unbounds \/ s' IN limits ==>
      imp_siwl_state_extends to_var_set vars rho s s'`;

val imp_siwl_in_result_def = Define `
  imp_siwl_in_result bhv s normals unbounds limits <=>
    case bhv of
      ImpSiwlCnormal => s IN normals
    | ImpSiwlCunboundVar => s IN unbounds
    | ImpSiwlCloopLimit => s IN limits`;

val imp_siwl_head_spec_def = Define `
  imp_siwl_head_spec get sigma constr rho to_var_set vars
      n ctr e c s normals unbounds limits <=>
    imp_siwl_results_extend to_var_set vars rho
      s normals unbounds limits /\
    (imp_siwl_is_solution (rho s) (constr s) ==>
     !gamma' bhv.
       imp_siwl_exec_while
         (SOME n) ctr
         (imp_siwl_compose get (rho s) (sigma s))
         e c gamma' bhv ==>
       ?s'.
         imp_siwl_in_result
           bhv s' normals unbounds limits /\
         imp_siwl_is_solution (rho s') (constr s') /\
         gamma' =
           imp_siwl_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_siwl_in_result
         bhv s' normals unbounds limits ==>
       imp_siwl_is_solution (rho s') (constr s') ==>
       imp_siwl_is_solution (rho s) (constr s) /\
       imp_siwl_exec_while
         (SOME n) ctr
         (imp_siwl_compose get (rho s) (sigma s))
         e c
         (imp_siwl_compose get (rho s') (sigma s'))
         bhv)`;

val imp_siwl_list_spec_def = Define `
  imp_siwl_list_spec get sigma constr rho to_var_set vars
      n ctr e c ss normals unbounds limits <=>
    (!s'.
       s' IN normals \/ s' IN unbounds \/ s' IN limits ==>
       ?s.
         s IN set ss /\
         imp_siwl_state_extends to_var_set vars rho s s') /\
    (!s.
       s IN set ss ==>
       imp_siwl_is_solution (rho s) (constr s) ==>
       !gamma' bhv.
         imp_siwl_exec_while
           (SOME n) ctr
           (imp_siwl_compose get (rho s) (sigma s))
           e c gamma' bhv ==>
         ?s'.
           imp_siwl_in_result
             bhv s' normals unbounds limits /\
           imp_siwl_is_solution (rho s') (constr s') /\
           gamma' =
             imp_siwl_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_siwl_in_result
         bhv s' normals unbounds limits ==>
       imp_siwl_is_solution (rho s') (constr s') ==>
       ?s.
         s IN set ss /\
         imp_siwl_is_solution (rho s) (constr s) /\
         imp_siwl_exec_while
           (SOME n) ctr
           (imp_siwl_compose get (rho s) (sigma s))
           e c
           (imp_siwl_compose get (rho s') (sigma s'))
           bhv)`;

val imp_SymbolicInterpreter_symbolic_interp_while_list_vc =
  ``!(get : 'a -> 'b -> 'c option)
      (sigma : 'd -> 'a)
      (constr : 'd -> 'c imp_siwl_constr)
      (rho : 'd -> 'c -> int)
      (to_var_set : 'e -> 'c set)
      (vars : 'd -> 'e)
      (ctr : int)
      (n : int)
      (ss : 'd list)
      (e : 'b imp_siwl_expr)
      (c : 'b imp_siwl_cmd).
      (!vs. FINITE (to_var_set vs)) /\
      (!s.
         FINITE s ==>
         ?vs. to_var_set vs = s) /\
      (!s.
         imp_siwl_vars_in_constraint (constr s) SUBSET
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
         imp_siwl_vars_in_constraint con SUBSET
           to_var_set vs /\
         (!x v.
            get sig x = SOME v ==>
            v IN to_var_set vs) ==>
         ?s.
           sigma s = sig /\
           constr s = con /\
           vars s = vs /\
           rho s = r) /\
      (0 : int) <= ctr /\
      ctr <= n
      ==>
      ((case ss of
          [] => T
        | s :: ss' =>
            (((0 : int) <= &(LENGTH ss) /\
              (0 : int) < &(LENGTH ss)) /\
             (0 : int) <= ctr /\
             ctr <= n) /\
            !normals1 unbounds1 limits1.
              FINITE normals1 /\
              FINITE unbounds1 /\
              FINITE limits1
              ==>
              (imp_siwl_head_spec
                 get sigma constr rho to_var_set vars
                 n ctr e c s normals1 unbounds1 limits1
               ==>
               (((0 : int) <= &(LENGTH ss) /\
                 LENGTH ss' < LENGTH ss) /\
                (0 : int) <= ctr /\
                ctr <= n))) /\
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
                 imp_siwl_head_spec
                   get sigma constr rho to_var_set vars
                   n ctr e c s normals1 unbounds1 limits1 /\
                 ?normals2 unbounds2 limits2.
                   FINITE normals2 /\
                   FINITE unbounds2 /\
                   FINITE limits2 /\
                   imp_siwl_list_spec
                     get sigma constr rho to_var_set vars
                     n ctr e c ss'
                     normals2 unbounds2 limits2 /\
                   limits = limits1 UNION limits2 /\
                   unbounds = unbounds1 UNION unbounds2 /\
                   normals = normals1 UNION normals2)
          ==>
          imp_siwl_list_spec
            get sigma constr rho to_var_set vars
            n ctr e c ss normals unbounds limits))``;
