(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmdqtvc: a verification
  condition for symbolic interpretation of commands, preserving symbolic-state
  extension and soundness and completeness with respect to bounded concrete
  command semantics. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory listTheory pred_setTheory;

Datatype:
  imp_si_expr =
    ImpSiElit int
  | ImpSiEvar 'var
  | ImpSiEsub imp_si_expr imp_si_expr
End

Datatype:
  imp_si_cmd =
    ImpSiCskip
  | ImpSiCassign 'var ('var imp_si_expr)
  | ImpSiCseq imp_si_cmd imp_si_cmd
  | ImpSiCif ('var imp_si_expr) imp_si_cmd imp_si_cmd
  | ImpSiCwhile ('var imp_si_expr) imp_si_cmd
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
  imp_si_symbolic_expr =
    ImpSiSlit int
  | ImpSiSvar 'svar
  | ImpSiSsub
      imp_si_symbolic_expr
      imp_si_symbolic_expr
End

Datatype:
  imp_si_constr =
    ImpSiCtrue
  | ImpSiCfalse
  | ImpSiCeq
      ('svar imp_si_symbolic_expr)
      ('svar imp_si_symbolic_expr)
  | ImpSiCneq
      ('svar imp_si_symbolic_expr)
      ('svar imp_si_symbolic_expr)
  | ImpSiCconj imp_si_constr imp_si_constr
  | ImpSiCexists 'svar imp_si_constr
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

val imp_si_state_valid_def = Define `
  imp_si_state_valid get sigma constr to_var_set vars s <=>
    imp_si_vars_in_constraint (constr s) SUBSET
      to_var_set (vars s) /\
    !x v.
      get (sigma s) x = SOME v ==>
      v IN to_var_set (vars s)`;

val imp_si_fields_def = Define `
  imp_si_fields sigma constr rho vars s sig con r vs <=>
    sigma s = sig /\
    constr s = con /\
    rho s = r /\
    vars s = vs`;

val imp_si_symbolic_match_def = Define `
  imp_si_symbolic_match get sigma rho s e se <=>
    imp_si_eval_expr
      (imp_si_compose get (rho s) (sigma s)) e =
      ImpSiEnormal (imp_si_interp_symbolic_expr (rho s) se) /\
    !v.
      v IN imp_si_vars_in_symbolic_expr se ==>
      ?x. get (sigma s) x = SOME v`;

val imp_si_rewrite_constraint_def = Define `
  imp_si_rewrite_constraint get sigma constr s x v' se con' <=>
    let con =
      ImpSiCconj (constr s) (ImpSiCeq (ImpSiSvar v') se)
    in
      (?v.
         (case get (sigma s) x of
            NONE => F
          | SOME v1 => v = v1) /\
         (!r.
            imp_si_is_solution r con' =
            imp_si_is_solution r (ImpSiCexists v con)) /\
         imp_si_vars_in_constraint con' SUBSET
           imp_si_vars_in_constraint (ImpSiCexists v con)) \/
      get (sigma s) x = NONE /\ con' = con`;

val imp_si_empty_results_def = Define `
  imp_si_empty_results normals unbounds limits <=>
    (limits = {} /\ &(CARD limits) = (0 : int)) /\
    (unbounds = {} /\ &(CARD unbounds) = (0 : int)) /\
    normals = {} /\ &(CARD normals) = (0 : int)`;

val imp_si_single_normal_def = Define `
  imp_si_single_normal s normals unbounds limits <=>
    (limits = {} /\ &(CARD limits) = (0 : int)) /\
    (unbounds = {} /\ &(CARD unbounds) = (0 : int)) /\
    normals = {s} /\ &(CARD normals) = (1 : int)`;

val imp_si_single_unbound_def = Define `
  imp_si_single_unbound s normals unbounds limits <=>
    (limits = {} /\ &(CARD limits) = (0 : int)) /\
    (unbounds = {s} /\ &(CARD unbounds) = (1 : int)) /\
    normals = {} /\ &(CARD normals) = (0 : int)`;

val imp_si_cmd_spec_def = Define `
  imp_si_cmd_spec get sigma constr rho to_var_set vars n c
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

val imp_si_while_spec_def = Define `
  imp_si_while_spec get sigma constr rho to_var_set vars n e c
      s normals unbounds limits <=>
    imp_si_results_extend to_var_set vars rho
      s normals unbounds limits /\
    (imp_si_is_solution (rho s) (constr s) ==>
     !gamma' bhv.
       imp_si_exec_while
         (SOME n) (0 : int)
         (imp_si_compose get (rho s) (sigma s))
         e c gamma' bhv ==>
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
       imp_si_exec_while
         (SOME n) (0 : int)
         (imp_si_compose get (rho s) (sigma s))
         e c
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

val imp_si_is_subcommand_def = Define `
  imp_si_is_subcommand parent child <=>
    case parent of
      ImpSiCskip => F
    | ImpSiCassign x e => F
    | ImpSiCseq c1 c2 => c1 = child \/ c2 = child
    | ImpSiCif e c1 c2 => c1 = child \/ c2 = child
    | ImpSiCwhile e c => c = child`;

val imp_si_assign_results_def = Define `
  imp_si_assign_results
      get set_sigma sigma constr rho to_var_set vars
      s x e normals unbounds limits <=>
    (?se.
       imp_si_symbolic_match get sigma rho s e se /\
       ?v'.
         v' NOTIN to_var_set (vars s) /\
         let sig' = set_sigma (sigma s) x v'
         in
           get sig' x = SOME v' /\
           (!k'. k' <> x ==> get sig' k' = get (sigma s) k') /\
           ?con'.
             imp_si_rewrite_constraint
               get sigma constr s x v' se con' /\
             ?vs'.
               to_var_set vs' =
                 v' INSERT to_var_set (vars s) /\
               (if v' IN to_var_set (vars s) then
                  CARD (to_var_set vs') =
                  CARD (to_var_set (vars s))
                else
                  &(CARD (to_var_set vs')) =
                  &(CARD (to_var_set (vars s))) + (1 : int)) /\
               ?s'.
                 imp_si_fields
                   sigma constr rho vars s'
                   sig' con'
                   (\w.
                      if w = v' then
                        imp_si_interp_symbolic_expr (rho s) se
                      else rho s w)
                   vs' /\
                 imp_si_single_normal
                   s' normals unbounds limits) \/
    (imp_si_eval_expr
       (imp_si_compose get (rho s) (sigma s)) e =
       ImpSiEunboundVar /\
     imp_si_single_unbound s normals unbounds limits)`;

val imp_si_seq_results_def = Define `
  imp_si_seq_results
      get sigma constr rho to_var_set vars to_state_list
      n s c1 c2 normals unbounds limits <=>
    ?normals1 unbounds1 limits1.
      FINITE normals1 /\
      FINITE unbounds1 /\
      FINITE limits1 /\
      imp_si_cmd_spec
        get sigma constr rho to_var_set vars n c1
        s normals1 unbounds1 limits1 /\
      let ss = to_state_list normals1
      in
        (!e. e IN normals1 <=> MEM e ss) /\
        ?unbounds2 limits2.
          FINITE unbounds2 /\
          FINITE limits2 /\
          imp_si_list_spec
            get sigma constr rho to_var_set vars n c2
            ss normals unbounds2 limits2 /\
          limits = limits1 UNION limits2 /\
          unbounds = unbounds1 UNION unbounds2`;

val imp_si_if_results_def = Define `
  imp_si_if_results
      get sigma constr rho to_var_set vars n
      s e c1 c2 normals unbounds limits <=>
    (?se.
       imp_si_symbolic_match get sigma rho s e se /\
       ?s1.
         imp_si_fields sigma constr rho vars s1
           (sigma s)
           (ImpSiCconj
             (constr s) (ImpSiCneq se (ImpSiSlit (0 : int))))
           (rho s) (vars s) /\
         ?s2.
           imp_si_fields sigma constr rho vars s2
             (sigma s)
             (ImpSiCconj
               (constr s) (ImpSiCeq se (ImpSiSlit (0 : int))))
             (rho s) (vars s) /\
           ?normals1 unbounds1 limits1.
             FINITE normals1 /\
             FINITE unbounds1 /\
             FINITE limits1 /\
             (?enabled.
                (enabled = F ==>
                 !r. ~imp_si_is_solution r (constr s1)) /\
                (if enabled = T then
                   imp_si_cmd_spec
                     get sigma constr rho to_var_set vars n c1
                     s1 normals1 unbounds1 limits1
                 else
                   imp_si_empty_results
                     normals1 unbounds1 limits1)) /\
             ?normals2 unbounds2 limits2.
               FINITE normals2 /\
               FINITE unbounds2 /\
               FINITE limits2 /\
               (?enabled.
                  (enabled = F ==>
                   !r. ~imp_si_is_solution r (constr s2)) /\
                  (if enabled = T then
                     imp_si_cmd_spec
                       get sigma constr rho to_var_set vars n c2
                       s2 normals2 unbounds2 limits2
                   else
                     imp_si_empty_results
                       normals2 unbounds2 limits2)) /\
               limits = limits1 UNION limits2 /\
               unbounds = unbounds1 UNION unbounds2 /\
               normals = normals1 UNION normals2) \/
    (imp_si_eval_expr
       (imp_si_compose get (rho s) (sigma s)) e =
       ImpSiEunboundVar /\
     imp_si_single_unbound s normals unbounds limits)`;

val imp_SymbolicInterpreter_symbolic_interp_cmd_vc =
  ``!(get : 'sigma -> 'var -> 'svar option)
      (set_sigma : 'sigma -> 'var -> 'svar -> 'sigma)
      (sigma : 'state -> 'sigma)
      (constr : 'state -> 'svar imp_si_constr)
      (rho : 'state -> 'svar -> int)
      (to_var_set : 'varset -> 'svar set)
      (vars : 'state -> 'varset)
      (to_state_list : 'state set -> 'state list)
      (n : int)
      (c : 'var imp_si_cmd)
      (s : 'state).
      (!vs. FINITE (to_var_set vs)) /\
      (!fs.
         FINITE fs ==>
         ?vs. to_var_set vs = fs) /\
      (!sig x v.
         get (set_sigma sig x v) x = SOME v) /\
      (!sig x v k.
         k <> x ==>
         get (set_sigma sig x v) k = get sig k) /\
      (!st. imp_si_state_valid
              get sigma constr to_var_set vars st) /\
      (!a b.
         sigma a = sigma b /\
         constr a = constr b /\
         rho a = rho b /\
         vars a = vars b ==>
         a = b) /\
      (!sig con r vs.
         imp_si_vars_in_constraint con SUBSET
           to_var_set vs /\
         (!x v.
            get sig x = SOME v ==>
            v IN to_var_set vs) ==>
         ?st.
           imp_si_fields sigma constr rho vars
             st sig con r vs) /\
      (!states e.
         FINITE states ==>
         (e IN states <=> MEM e (to_state_list states))) /\
      (0 : int) <= n
      ==>
      ((case c of
          ImpSiCskip => T
        | ImpSiCassign x e =>
            !se.
              imp_si_symbolic_match get sigma rho s e se ==>
              !v'.
                v' NOTIN to_var_set (vars s) ==>
                let sig' = set_sigma (sigma s) x v'
                in
                  get sig' x = SOME v' /\
                  (!k'.
                     k' <> x ==>
                     get sig' k' = get (sigma s) k') ==>
                  !con'.
                    imp_si_rewrite_constraint
                      get sigma constr s x v' se con' ==>
                    !vs'.
                      to_var_set vs' =
                        v' INSERT to_var_set (vars s) /\
                      (if v' IN to_var_set (vars s) then
                         CARD (to_var_set vs') =
                         CARD (to_var_set (vars s))
                       else
                         &(CARD (to_var_set vs')) =
                         &(CARD (to_var_set (vars s))) +
                           (1 : int)) ==>
                      imp_si_vars_in_constraint con' SUBSET
                        to_var_set vs' /\
                      !x1 v.
                        get sig' x1 = SOME v ==>
                        v IN to_var_set vs'
        | ImpSiCseq c1 c2 =>
            (imp_si_is_subcommand c c1 /\
             (0 : int) <= n) /\
            !normals1 unbounds1 limits1.
              FINITE normals1 /\
              FINITE unbounds1 /\
              FINITE limits1 /\
              imp_si_cmd_spec
                get sigma constr rho to_var_set vars n c1
                s normals1 unbounds1 limits1
              ==>
              let ss = to_state_list normals1
              in
                (!e. e IN normals1 <=> MEM e ss) ==>
                ((imp_si_is_subcommand c c2 \/
                  c = c2 /\
                  (0 : int) <= (0 : int) /\
                  &(LENGTH ss) < (0 : int)) /\
                 (0 : int) <= n)
        | ImpSiCif e c1 c2 =>
            !se.
              imp_si_symbolic_match get sigma rho s e se ==>
              let vs1 = vars s;
                  con1 =
                    ImpSiCconj
                      (constr s)
                      (ImpSiCneq se (ImpSiSlit (0 : int)));
                  sig1 = sigma s
              in
                imp_si_vars_in_constraint con1 SUBSET
                  to_var_set vs1 /\
                (!x v.
                   get sig1 x = SOME v ==>
                   v IN to_var_set vs1) /\
                !s1.
                  imp_si_fields sigma constr rho vars
                    s1 sig1 con1 (rho s) vs1 ==>
                  let vs2 = vars s;
                      con2 =
                        ImpSiCconj
                          (constr s)
                          (ImpSiCeq se (ImpSiSlit (0 : int)));
                      sig2 = sigma s
                  in
                    imp_si_vars_in_constraint con2 SUBSET
                      to_var_set vs2 /\
                    (!x v.
                       get sig2 x = SOME v ==>
                       v IN to_var_set vs2) /\
                    !s2.
                      imp_si_fields sigma constr rho vars
                        s2 sig2 con2 (rho s) vs2 ==>
                      (((T = F ==>
                         !r. ~imp_si_is_solution r (constr s1)) ==>
                        imp_si_is_subcommand c c1 /\
                        (0 : int) <= n) /\
                       !normals1 unbounds1 limits1.
                         FINITE normals1 /\
                         FINITE unbounds1 /\
                         FINITE limits1 /\
                         (?enabled.
                            (enabled = F ==>
                             !r.
                               ~imp_si_is_solution
                                 r (constr s1)) /\
                            (if enabled = T then
                               imp_si_cmd_spec
                                 get sigma constr rho
                                 to_var_set vars n c1
                                 s1 normals1 unbounds1 limits1
                             else
                               imp_si_empty_results
                                 normals1 unbounds1 limits1))
                         ==>
                         ((T = F ==>
                           !r.
                             ~imp_si_is_solution
                               r (constr s2)) ==>
                          imp_si_is_subcommand c c2 /\
                          (0 : int) <= n))
        | ImpSiCwhile e c1 =>
            ((imp_si_is_subcommand c (ImpSiCwhile e c1) \/
              c = ImpSiCwhile e c1 /\
              (0 : int) <= n + (1 : int) /\
              n - (0 : int) < n + (1 : int)) /\
             (0 : int) <= (0 : int) /\
             (0 : int) <= n)) /\
       !normals unbounds limits.
         FINITE normals /\
         FINITE unbounds /\
         FINITE limits
         ==>
         ((case c of
             ImpSiCskip =>
               imp_si_single_normal
                 s normals unbounds limits
           | ImpSiCassign x e =>
               imp_si_assign_results
                 get set_sigma sigma constr rho
                 to_var_set vars s x e
                 normals unbounds limits
           | ImpSiCseq c1 c2 =>
               imp_si_seq_results
                 get sigma constr rho to_var_set vars
                 to_state_list n s c1 c2
                 normals unbounds limits
           | ImpSiCif e c1 c2 =>
               imp_si_if_results
                 get sigma constr rho to_var_set vars n
                 s e c1 c2 normals unbounds limits
           | ImpSiCwhile e c1 =>
               imp_si_while_spec
                 get sigma constr rho to_var_set vars n e c1
                 s normals unbounds limits)
          ==>
          imp_si_cmd_spec
            get sigma constr rho to_var_set vars n c
            s normals unbounds limits))``;
