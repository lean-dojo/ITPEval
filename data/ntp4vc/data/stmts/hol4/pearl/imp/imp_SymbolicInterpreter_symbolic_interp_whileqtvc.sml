(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_whileqtvc: the bounded
  symbolic-interpreter while-loop verification condition, relating symbolic
  branch construction and finite result sets to sound and complete concrete
  IMP loop executions with state extension. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory listTheory pred_setTheory;

Datatype:
  'var imp_siw_expr =
    ImpSiwElit int
  | ImpSiwEvar 'var
  | ImpSiwEsub ('var imp_siw_expr) ('var imp_siw_expr)
End

Datatype:
  'var imp_siw_cmd =
    ImpSiwCskip
  | ImpSiwCassign 'var ('var imp_siw_expr)
  | ImpSiwCseq ('var imp_siw_cmd) ('var imp_siw_cmd)
  | ImpSiwCif
      ('var imp_siw_expr)
      ('var imp_siw_cmd)
      ('var imp_siw_cmd)
  | ImpSiwCwhile ('var imp_siw_expr) ('var imp_siw_cmd)
End

Datatype:
  imp_siw_expr_behaviour =
    ImpSiwEnormal int
  | ImpSiwEunboundVar
End

Datatype:
  imp_siw_behaviour =
    ImpSiwCnormal
  | ImpSiwCunboundVar
  | ImpSiwCloopLimit
End

val imp_siw_eval_expr_def = Define `
  (imp_siw_eval_expr env (ImpSiwElit n) = ImpSiwEnormal n) /\
  (imp_siw_eval_expr env (ImpSiwEvar x) =
     case env x of
       NONE => ImpSiwEunboundVar
     | SOME n => ImpSiwEnormal n) /\
  (imp_siw_eval_expr env (ImpSiwEsub e1 e2) =
     case imp_siw_eval_expr env e1 of
       ImpSiwEunboundVar => ImpSiwEunboundVar
     | ImpSiwEnormal n1 =>
         case imp_siw_eval_expr env e2 of
           ImpSiwEunboundVar => ImpSiwEunboundVar
         | ImpSiwEnormal n2 => ImpSiwEnormal (n1 - n2))`;

val _ = Hol_reln `
  (!limit env.
     imp_siw_exec_cmd
       limit env ImpSiwCskip env ImpSiwCnormal) /\
  (!limit env e n v.
     imp_siw_eval_expr env e = ImpSiwEnormal n ==>
     imp_siw_exec_cmd
       limit env (ImpSiwCassign v e)
       (\x. if x = v then SOME n else env x)
       ImpSiwCnormal) /\
  (!limit env e v.
     imp_siw_eval_expr env e = ImpSiwEunboundVar ==>
     imp_siw_exec_cmd
       limit env (ImpSiwCassign v e) env ImpSiwCunboundVar) /\
  (!limit env1 c1 env2 c2 env3 bhv.
     imp_siw_exec_cmd limit env1 c1 env2 ImpSiwCnormal /\
     imp_siw_exec_cmd limit env2 c2 env3 bhv ==>
     imp_siw_exec_cmd
       limit env1 (ImpSiwCseq c1 c2) env3 bhv) /\
  (!limit env1 c1 env2 bhv c2.
     imp_siw_exec_cmd limit env1 c1 env2 bhv /\
     bhv <> ImpSiwCnormal ==>
     imp_siw_exec_cmd
       limit env1 (ImpSiwCseq c1 c2) env2 bhv) /\
  (!limit env e c1 c2 env' bhv.
     imp_siw_eval_expr env e = ImpSiwEnormal (0 : int) /\
     imp_siw_exec_cmd limit env c2 env' bhv ==>
     imp_siw_exec_cmd
       limit env (ImpSiwCif e c1 c2) env' bhv) /\
  (!limit env e n c1 c2 env' bhv.
     n <> (0 : int) /\
     imp_siw_eval_expr env e = ImpSiwEnormal n /\
     imp_siw_exec_cmd limit env c1 env' bhv ==>
     imp_siw_exec_cmd
       limit env (ImpSiwCif e c1 c2) env' bhv) /\
  (!limit env e c1 c2.
     imp_siw_eval_expr env e = ImpSiwEunboundVar ==>
     imp_siw_exec_cmd
       limit env (ImpSiwCif e c1 c2) env ImpSiwCunboundVar) /\
  (!limit env e c env' bhv.
     imp_siw_exec_while
       limit (0 : int) env e c env' bhv ==>
     imp_siw_exec_cmd
       limit env (ImpSiwCwhile e c) env' bhv) /\
  (!limit ctr env e c.
     (case limit of
        NONE => F
      | SOME n => n <= ctr) ==>
     imp_siw_exec_while
       limit ctr env e c env ImpSiwCloopLimit) /\
  (!limit ctr env e c.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siw_eval_expr env e = ImpSiwEnormal (0 : int) ==>
     imp_siw_exec_while
       limit ctr env e c env ImpSiwCnormal) /\
  (!limit ctr env e c.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siw_eval_expr env e = ImpSiwEunboundVar ==>
     imp_siw_exec_while
       limit ctr env e c env ImpSiwCunboundVar) /\
  (!limit ctr env1 e v c env2 bhv.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siw_eval_expr env1 e = ImpSiwEnormal v /\
     v <> (0 : int) /\
     imp_siw_exec_cmd limit env1 c env2 bhv /\
     bhv <> ImpSiwCnormal ==>
     imp_siw_exec_while
       limit ctr env1 e c env2 bhv) /\
  (!limit ctr env1 e v c env2 env3 bhv.
     (case limit of
        NONE => T
      | SOME n => ctr < n) /\
     imp_siw_eval_expr env1 e = ImpSiwEnormal v /\
     v <> (0 : int) /\
     imp_siw_exec_cmd limit env1 c env2 ImpSiwCnormal /\
     imp_siw_exec_while
       limit (ctr + (1 : int)) env2 e c env3 bhv ==>
     imp_siw_exec_while
       limit ctr env1 e c env3 bhv)
`;

Datatype:
  'svar imp_siw_symbolic_expr =
    ImpSiwSlit int
  | ImpSiwSvar 'svar
  | ImpSiwSsub
      ('svar imp_siw_symbolic_expr)
      ('svar imp_siw_symbolic_expr)
End

Datatype:
  'svar imp_siw_constr =
    ImpSiwCtrue
  | ImpSiwCfalse
  | ImpSiwCeq
      ('svar imp_siw_symbolic_expr)
      ('svar imp_siw_symbolic_expr)
  | ImpSiwCneq
      ('svar imp_siw_symbolic_expr)
      ('svar imp_siw_symbolic_expr)
  | ImpSiwCconj
      ('svar imp_siw_constr)
      ('svar imp_siw_constr)
  | ImpSiwCexists 'svar ('svar imp_siw_constr)
End

val imp_siw_interp_symbolic_expr_def = Define `
  (imp_siw_interp_symbolic_expr rho (ImpSiwSlit n) = n) /\
  (imp_siw_interp_symbolic_expr rho (ImpSiwSvar v) = rho v) /\
  (imp_siw_interp_symbolic_expr rho (ImpSiwSsub e1 e2) =
     imp_siw_interp_symbolic_expr rho e1 -
     imp_siw_interp_symbolic_expr rho e2)`;

val imp_siw_is_solution_def = Define `
  (imp_siw_is_solution rho ImpSiwCtrue = T) /\
  (imp_siw_is_solution rho ImpSiwCfalse = F) /\
  (imp_siw_is_solution rho (ImpSiwCeq e1 e2) =
     (imp_siw_interp_symbolic_expr rho e1 =
      imp_siw_interp_symbolic_expr rho e2)) /\
  (imp_siw_is_solution rho (ImpSiwCneq e1 e2) =
     (imp_siw_interp_symbolic_expr rho e1 <>
      imp_siw_interp_symbolic_expr rho e2)) /\
  (imp_siw_is_solution rho (ImpSiwCconj c1 c2) =
     (imp_siw_is_solution rho c1 /\
      imp_siw_is_solution rho c2)) /\
  (imp_siw_is_solution rho (ImpSiwCexists v c) =
     imp_siw_is_solution rho c)`;

val imp_siw_vars_in_symbolic_expr_def = Define `
  (imp_siw_vars_in_symbolic_expr (ImpSiwSlit n) = {}) /\
  (imp_siw_vars_in_symbolic_expr (ImpSiwSvar v) = {v}) /\
  (imp_siw_vars_in_symbolic_expr (ImpSiwSsub e1 e2) =
     imp_siw_vars_in_symbolic_expr e1 UNION
     imp_siw_vars_in_symbolic_expr e2)`;

val imp_siw_vars_in_constraint_def = Define `
  (imp_siw_vars_in_constraint ImpSiwCtrue = {}) /\
  (imp_siw_vars_in_constraint ImpSiwCfalse = {}) /\
  (imp_siw_vars_in_constraint (ImpSiwCeq e1 e2) =
     imp_siw_vars_in_symbolic_expr e1 UNION
     imp_siw_vars_in_symbolic_expr e2) /\
  (imp_siw_vars_in_constraint (ImpSiwCneq e1 e2) =
     imp_siw_vars_in_symbolic_expr e1 UNION
     imp_siw_vars_in_symbolic_expr e2) /\
  (imp_siw_vars_in_constraint (ImpSiwCconj c1 c2) =
     imp_siw_vars_in_constraint c1 UNION
     imp_siw_vars_in_constraint c2) /\
  (imp_siw_vars_in_constraint (ImpSiwCexists v c) =
     v INSERT imp_siw_vars_in_constraint c)`;

val imp_siw_compose_def = Define `
  imp_siw_compose get rho sigma x =
    case get sigma x of
      NONE => NONE
    | SOME v => SOME (rho v)`;

val imp_siw_state_extends_def = Define `
  imp_siw_state_extends to_var_set vars rho s s' <=>
    to_var_set (vars s) SUBSET to_var_set (vars s') /\
    !v.
      v IN to_var_set (vars s) ==>
      rho s v = rho s' v`;

val imp_siw_results_extend_def = Define `
  imp_siw_results_extend to_var_set vars rho
      s normals unbounds limits <=>
    !s'.
      s' IN normals \/ s' IN unbounds \/ s' IN limits ==>
      imp_siw_state_extends to_var_set vars rho s s'`;

val imp_siw_in_result_def = Define `
  imp_siw_in_result bhv s normals unbounds limits <=>
    case bhv of
      ImpSiwCnormal => s IN normals
    | ImpSiwCunboundVar => s IN unbounds
    | ImpSiwCloopLimit => s IN limits`;

val imp_siw_state_valid_def = Define `
  imp_siw_state_valid get sigma constr to_var_set vars s <=>
    imp_siw_vars_in_constraint (constr s) SUBSET
      to_var_set (vars s) /\
    !x v.
      get (sigma s) x = SOME v ==>
      v IN to_var_set (vars s)`;

val imp_siw_components_valid_def = Define `
  imp_siw_components_valid get to_var_set sig con vs <=>
    imp_siw_vars_in_constraint con SUBSET to_var_set vs /\
    !x v.
      get sig x = SOME v ==>
      v IN to_var_set vs`;

val imp_siw_fields_def = Define `
  imp_siw_fields sigma constr rho vars s sig con r vs <=>
    sigma s = sig /\
    constr s = con /\
    rho s = r /\
    vars s = vs`;

val imp_siw_symbolic_match_def = Define `
  imp_siw_symbolic_match get sigma rho s e se <=>
    imp_siw_eval_expr
      (imp_siw_compose get (rho s) (sigma s)) e =
      ImpSiwEnormal (imp_siw_interp_symbolic_expr (rho s) se) /\
    !v.
      v IN imp_siw_vars_in_symbolic_expr se ==>
      ?x. get (sigma s) x = SOME v`;

val imp_siw_empty_results_def = Define `
  imp_siw_empty_results normals unbounds limits <=>
    (limits = {} /\ &(CARD limits) = (0 : int)) /\
    (unbounds = {} /\ &(CARD unbounds) = (0 : int)) /\
    normals = {} /\ &(CARD normals) = (0 : int)`;

val imp_siw_single_normal_def = Define `
  imp_siw_single_normal s normals unbounds limits <=>
    (limits = {} /\ &(CARD limits) = (0 : int)) /\
    (unbounds = {} /\ &(CARD unbounds) = (0 : int)) /\
    normals = {s} /\ &(CARD normals) = (1 : int)`;

val imp_siw_single_unbound_def = Define `
  imp_siw_single_unbound s normals unbounds limits <=>
    (limits = {} /\ &(CARD limits) = (0 : int)) /\
    (unbounds = {s} /\ &(CARD unbounds) = (1 : int)) /\
    normals = {} /\ &(CARD normals) = (0 : int)`;

val imp_siw_single_limit_def = Define `
  imp_siw_single_limit s normals unbounds limits <=>
    (limits = {s} /\ &(CARD limits) = (1 : int)) /\
    (unbounds = {} /\ &(CARD unbounds) = (0 : int)) /\
    normals = {} /\ &(CARD normals) = (0 : int)`;

val imp_siw_cmd_spec_def = Define `
  imp_siw_cmd_spec get sigma constr rho to_var_set vars n c
      s normals unbounds limits <=>
    imp_siw_results_extend to_var_set vars rho
      s normals unbounds limits /\
    (imp_siw_is_solution (rho s) (constr s) ==>
     !gamma' bhv.
       imp_siw_exec_cmd
         (SOME n)
         (imp_siw_compose get (rho s) (sigma s))
         c gamma' bhv ==>
       ?s'.
         imp_siw_in_result
           bhv s' normals unbounds limits /\
         imp_siw_is_solution (rho s') (constr s') /\
         gamma' =
           imp_siw_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_siw_in_result
         bhv s' normals unbounds limits ==>
       imp_siw_is_solution (rho s') (constr s') ==>
       imp_siw_is_solution (rho s) (constr s) /\
       imp_siw_exec_cmd
         (SOME n)
         (imp_siw_compose get (rho s) (sigma s))
         c
         (imp_siw_compose get (rho s') (sigma s'))
         bhv)`;

val imp_siw_while_spec_def = Define `
  imp_siw_while_spec get sigma constr rho to_var_set vars
      n ctr e c s normals unbounds limits <=>
    imp_siw_results_extend to_var_set vars rho
      s normals unbounds limits /\
    (imp_siw_is_solution (rho s) (constr s) ==>
     !gamma' bhv.
       imp_siw_exec_while
         (SOME n) ctr
         (imp_siw_compose get (rho s) (sigma s))
         e c gamma' bhv ==>
       ?s'.
         imp_siw_in_result
           bhv s' normals unbounds limits /\
         imp_siw_is_solution (rho s') (constr s') /\
         gamma' =
           imp_siw_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_siw_in_result
         bhv s' normals unbounds limits ==>
       imp_siw_is_solution (rho s') (constr s') ==>
       imp_siw_is_solution (rho s) (constr s) /\
       imp_siw_exec_while
         (SOME n) ctr
         (imp_siw_compose get (rho s) (sigma s))
         e c
         (imp_siw_compose get (rho s') (sigma s'))
         bhv)`;

val imp_siw_list_spec_def = Define `
  imp_siw_list_spec get sigma constr rho to_var_set vars
      n ctr e c ss normals unbounds limits <=>
    (!s'.
       s' IN normals \/ s' IN unbounds \/ s' IN limits ==>
       ?s.
         MEM s ss /\
         imp_siw_state_extends to_var_set vars rho s s') /\
    (!s.
       MEM s ss ==>
       imp_siw_is_solution (rho s) (constr s) ==>
       !gamma' bhv.
         imp_siw_exec_while
           (SOME n) ctr
           (imp_siw_compose get (rho s) (sigma s))
           e c gamma' bhv ==>
         ?s'.
           imp_siw_in_result
             bhv s' normals unbounds limits /\
           imp_siw_is_solution (rho s') (constr s') /\
           gamma' =
             imp_siw_compose get (rho s') (sigma s')) /\
    (!bhv s'.
       imp_siw_in_result
         bhv s' normals unbounds limits ==>
       imp_siw_is_solution (rho s') (constr s') ==>
       ?s.
         MEM s ss /\
         imp_siw_is_solution (rho s) (constr s) /\
         imp_siw_exec_while
           (SOME n) ctr
           (imp_siw_compose get (rho s) (sigma s))
           e c
           (imp_siw_compose get (rho s') (sigma s'))
           bhv)`;

val imp_siw_body_measure_def = Define `
  imp_siw_body_measure
      get sigma constr rho to_var_set vars to_state_list
      n ctr c s normals unbounds limits <=>
    imp_siw_cmd_spec
      get sigma constr rho to_var_set vars n c
      s normals unbounds limits ==>
    let normal_states = to_state_list normals
    in
      (!e. e IN normals <=> MEM e normal_states) ==>
      let next_ctr = ctr + (1 : int)
      in
        (((0 : int) <= n - ctr /\
          n - next_ctr < n - ctr) \/
         (n - ctr = n - next_ctr /\
          (0 : int) <= (0 : int) /\
          &(LENGTH normal_states) < (0 : int))) /\
        (0 : int) <= next_ctr /\
        next_ctr <= n`;

val imp_siw_recursive_branch_def = Define `
  imp_siw_recursive_branch
      get sigma constr rho to_var_set vars to_state_list
      n ctr e c s normals unbounds limits <=>
    ?enabled.
      (enabled = F ==>
       !r. ~imp_siw_is_solution r (constr s)) /\
      (if enabled = T then
         ?body_normals body_unbounds body_limits.
           FINITE body_normals /\
           FINITE body_unbounds /\
           FINITE body_limits /\
           imp_siw_cmd_spec
             get sigma constr rho to_var_set vars n c s
             body_normals body_unbounds body_limits /\
           let normal_states = to_state_list body_normals
           in
             (!x. x IN body_normals <=> MEM x normal_states) /\
             ?recursive_unbounds recursive_limits.
               FINITE recursive_unbounds /\
               FINITE recursive_limits /\
               imp_siw_list_spec
                 get sigma constr rho to_var_set vars
                 n (ctr + (1 : int)) e c normal_states
                 normals recursive_unbounds recursive_limits /\
               limits = body_limits UNION recursive_limits /\
               unbounds = body_unbounds UNION recursive_unbounds
       else
         imp_siw_empty_results normals unbounds limits)`;

val imp_siw_zero_branch_def = Define `
  imp_siw_zero_branch constr rho s normals unbounds limits <=>
    ?enabled.
      (enabled = F ==>
       !r. ~imp_siw_is_solution r (constr s)) /\
      (if enabled = T then
         imp_siw_single_normal s normals unbounds limits
       else
         imp_siw_empty_results normals unbounds limits)`;

val imp_siw_symbolic_step_def = Define `
  imp_siw_symbolic_step
      get sigma constr rho to_var_set vars to_state_list
      n ctr e c s normals unbounds limits <=>
    ?se.
      imp_siw_symbolic_match get sigma rho s e se /\
      ?nonzero_state.
        imp_siw_fields sigma constr rho vars nonzero_state
          (sigma s)
          (ImpSiwCconj
            (constr s) (ImpSiwCneq se (ImpSiwSlit (0 : int))))
          (rho s) (vars s) /\
        ?zero_state.
          imp_siw_fields sigma constr rho vars zero_state
            (sigma s)
            (ImpSiwCconj
              (constr s) (ImpSiwCeq se (ImpSiwSlit (0 : int))))
            (rho s) (vars s) /\
          ?nonzero_normals nonzero_unbounds nonzero_limits.
            FINITE nonzero_normals /\
            FINITE nonzero_unbounds /\
            FINITE nonzero_limits /\
            imp_siw_recursive_branch
              get sigma constr rho to_var_set vars to_state_list
              n ctr e c nonzero_state
              nonzero_normals nonzero_unbounds nonzero_limits /\
            ?zero_normals zero_unbounds zero_limits.
              FINITE zero_normals /\
              FINITE zero_unbounds /\
              FINITE zero_limits /\
              imp_siw_zero_branch constr rho zero_state
                zero_normals zero_unbounds zero_limits /\
              limits = nonzero_limits UNION zero_limits /\
              unbounds = nonzero_unbounds UNION zero_unbounds /\
              normals = nonzero_normals UNION zero_normals`;

val imp_siw_input_premise_def = Define `
  imp_siw_input_premise
      get sigma constr rho to_var_set vars to_state_list
      n ctr e c s normals unbounds limits <=>
    if ctr = n then
      imp_siw_single_limit s normals unbounds limits
    else
      imp_siw_symbolic_step
        get sigma constr rho to_var_set vars to_state_list
        n ctr e c s normals unbounds limits \/
      imp_siw_eval_expr
        (imp_siw_compose get (rho s) (sigma s)) e =
        ImpSiwEunboundVar /\
      imp_siw_single_unbound s normals unbounds limits`;

val imp_siw_construction_measure_def = Define `
  imp_siw_construction_measure
      get sigma constr rho to_var_set vars to_state_list
      n ctr e c s <=>
    ctr <> n ==>
    !se.
      imp_siw_symbolic_match get sigma rho s e se ==>
      let nonzero_con =
        ImpSiwCconj
          (constr s) (ImpSiwCneq se (ImpSiwSlit (0 : int)));
          zero_con =
        ImpSiwCconj
          (constr s) (ImpSiwCeq se (ImpSiwSlit (0 : int)))
      in
        imp_siw_components_valid
          get to_var_set (sigma s) nonzero_con (vars s) /\
        !nonzero_state.
          imp_siw_fields sigma constr rho vars nonzero_state
            (sigma s) nonzero_con (rho s) (vars s) ==>
          imp_siw_components_valid
            get to_var_set (sigma s) zero_con (vars s) /\
          !zero_state.
            imp_siw_fields sigma constr rho vars zero_state
              (sigma s) zero_con (rho s) (vars s) ==>
            (T = F ==>
             !r.
               ~imp_siw_is_solution r (constr nonzero_state)) ==>
            (0 : int) <= n /\
            !normals unbounds limits.
              FINITE normals /\
              FINITE unbounds /\
              FINITE limits ==>
              imp_siw_body_measure
                get sigma constr rho to_var_set vars to_state_list
                n ctr c nonzero_state normals unbounds limits`;

val imp_SymbolicInterpreter_symbolic_interp_while_vc =
  ``!(get : 'sigma -> 'var -> 'svar option)
      (sigma : 'state -> 'sigma)
      (constr : 'state -> 'svar imp_siw_constr)
      (rho : 'state -> 'svar -> int)
      (to_var_set : 'varset -> 'svar set)
      (vars : 'state -> 'varset)
      (to_state_list : 'state set -> 'state list)
      (ctr : int)
      (n : int)
      (s : 'state)
      (e : 'var imp_siw_expr)
      (c : 'var imp_siw_cmd).
      (!vs. FINITE (to_var_set vs)) /\
      (!fs.
         FINITE fs ==>
         ?vs. to_var_set vs = fs) /\
      (!st.
         imp_siw_state_valid
           get sigma constr to_var_set vars st) /\
      (!a b.
         sigma a = sigma b /\
         constr a = constr b /\
         rho a = rho b /\
         vars a = vars b ==>
         a = b) /\
      (!sig con vs r.
         imp_siw_components_valid
           get to_var_set sig con vs ==>
         ?st.
           imp_siw_fields
             sigma constr rho vars st sig con r vs) /\
      (!states x.
         FINITE states ==>
         (x IN states <=> MEM x (to_state_list states))) /\
      (0 : int) <= ctr /\
      ctr <= n
      ==>
      imp_siw_construction_measure
        get sigma constr rho to_var_set vars to_state_list
        n ctr e c s /\
      !normals unbounds limits.
        FINITE normals /\
        FINITE unbounds /\
        FINITE limits ==>
        imp_siw_input_premise
          get sigma constr rho to_var_set vars to_state_list
          n ctr e c s normals unbounds limits ==>
        imp_siw_while_spec
          get sigma constr rho to_var_set vars
          n ctr e c s normals unbounds limits``;
