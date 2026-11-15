(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_SymbolicInterpreter_symbolic_interp_exprqtvc: a verification
  condition for symbolic interpretation of literals, variables, and
  subtraction, including unbound-variable propagation and provenance of
  symbolic variables. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory pred_setTheory;

Datatype:
  imp_sie_expr =
    ImpSieElit int
  | ImpSieEvar 'var
  | ImpSieEsub imp_sie_expr imp_sie_expr
End

Datatype:
  imp_sie_expr_behaviour =
    ImpSieEnormal int
  | ImpSieEunboundVar
End

val (imp_sie_eval_expr_rules,
     imp_sie_eval_expr_ind,
     imp_sie_eval_expr_cases) =
  Hol_reln `
    (!env n.
       imp_sie_eval_expr env (ImpSieElit n) (ImpSieEnormal n)) /\
    (!env x n.
       env x = SOME n ==>
       imp_sie_eval_expr env (ImpSieEvar x) (ImpSieEnormal n)) /\
    (!env x.
       env x = NONE ==>
       imp_sie_eval_expr env (ImpSieEvar x) ImpSieEunboundVar) /\
    (!env e1 n1 e2 n2.
       imp_sie_eval_expr env e1 (ImpSieEnormal n1) /\
       imp_sie_eval_expr env e2 (ImpSieEnormal n2) ==>
       imp_sie_eval_expr
         env (ImpSieEsub e1 e2) (ImpSieEnormal (n1 - n2))) /\
    (!env e1 e2.
       imp_sie_eval_expr env e1 ImpSieEunboundVar ==>
       imp_sie_eval_expr env (ImpSieEsub e1 e2) ImpSieEunboundVar) /\
    (!env e1 n1 e2.
       imp_sie_eval_expr env e1 (ImpSieEnormal n1) /\
       imp_sie_eval_expr env e2 ImpSieEunboundVar ==>
       imp_sie_eval_expr env (ImpSieEsub e1 e2) ImpSieEunboundVar)
  `;

Datatype:
  imp_sie_symbolic_expr =
    ImpSieSlit int
  | ImpSieSvar 'svar
  | ImpSieSsub
      imp_sie_symbolic_expr
      imp_sie_symbolic_expr
End

Datatype:
  imp_sie_constraint =
    ImpSieCtrue
  | ImpSieCfalse
  | ImpSieCeq
      ('svar imp_sie_symbolic_expr)
      ('svar imp_sie_symbolic_expr)
  | ImpSieCneq
      ('svar imp_sie_symbolic_expr)
      ('svar imp_sie_symbolic_expr)
  | ImpSieCconj imp_sie_constraint imp_sie_constraint
  | ImpSieCexists 'svar imp_sie_constraint
End

val imp_sie_interp_symbolic_expr_def = Define `
  (imp_sie_interp_symbolic_expr rho (ImpSieSlit n) = n) /\
  (imp_sie_interp_symbolic_expr rho (ImpSieSvar v) = rho v) /\
  (imp_sie_interp_symbolic_expr rho (ImpSieSsub e1 e2) =
     imp_sie_interp_symbolic_expr rho e1 -
     imp_sie_interp_symbolic_expr rho e2)`;

val imp_sie_vars_in_symbolic_expr_def = Define `
  (imp_sie_vars_in_symbolic_expr (ImpSieSlit n) = {}) /\
  (imp_sie_vars_in_symbolic_expr (ImpSieSvar v) = {v}) /\
  (imp_sie_vars_in_symbolic_expr (ImpSieSsub e1 e2) =
     imp_sie_vars_in_symbolic_expr e1 UNION
     imp_sie_vars_in_symbolic_expr e2)`;

val imp_sie_vars_in_constraint_def = Define `
  (imp_sie_vars_in_constraint ImpSieCtrue = {}) /\
  (imp_sie_vars_in_constraint ImpSieCfalse = {}) /\
  (imp_sie_vars_in_constraint (ImpSieCeq e1 e2) =
     imp_sie_vars_in_symbolic_expr e1 UNION
     imp_sie_vars_in_symbolic_expr e2) /\
  (imp_sie_vars_in_constraint (ImpSieCneq e1 e2) =
     imp_sie_vars_in_symbolic_expr e1 UNION
     imp_sie_vars_in_symbolic_expr e2) /\
  (imp_sie_vars_in_constraint (ImpSieCconj c1 c2) =
     imp_sie_vars_in_constraint c1 UNION
     imp_sie_vars_in_constraint c2) /\
  (imp_sie_vars_in_constraint (ImpSieCexists v c) =
     v INSERT imp_sie_vars_in_constraint c)`;

val imp_sie_compose_def = Define `
  imp_sie_compose get rho sigma x =
    case get sigma x of
      NONE => NONE
    | SOME v => SOME (rho v)`;

val imp_SymbolicInterpreter_symbolic_interp_expr_vc =
  ``!(get : 'sigma -> 'var -> 'svar option)
      (sigma : 'state -> 'sigma)
      (rho : 'state -> 'svar -> int)
      (constr : 'state -> 'svar imp_sie_constraint)
      (vars : 'state -> 'svar set)
      (e : 'var imp_sie_expr)
      (s : 'state).
      FINITE (vars s) /\
      imp_sie_vars_in_constraint (constr s) SUBSET vars s /\
      (!x v.
         get (sigma s) x = SOME v ==>
         v IN vars s)
      ==>
      case e of
        ImpSieElit n =>
          (let result : 'svar imp_sie_symbolic_expr = ImpSieSlit n in
             imp_sie_eval_expr
               (imp_sie_compose get (rho s) (sigma s))
               e
               (ImpSieEnormal
                  (imp_sie_interp_symbolic_expr (rho s) result)) /\
             !v.
               v IN imp_sie_vars_in_symbolic_expr result ==>
               ?x. get (sigma s) x = SOME v)
      | ImpSieEvar x =>
          (!o1.
             get (sigma s) x = SOME o1 ==>
             (let result : 'svar imp_sie_symbolic_expr = ImpSieSvar o1 in
                imp_sie_eval_expr
                  (imp_sie_compose get (rho s) (sigma s))
                  e
                  (ImpSieEnormal
                     (imp_sie_interp_symbolic_expr (rho s) result)) /\
                !v.
                  v IN imp_sie_vars_in_symbolic_expr result ==>
                  ?x1. get (sigma s) x1 = SOME v)) /\
          (get (sigma s) x = NONE ==>
           imp_sie_eval_expr
             (imp_sie_compose get (rho s) (sigma s))
             e
             ImpSieEunboundVar)
      | ImpSieEsub e1 e2 =>
          (case e of
             ImpSieElit n => F
           | ImpSieEvar x => F
           | ImpSieEsub f f1 => f = e2 \/ f1 = e2) /\
          (!o1 : 'svar imp_sie_symbolic_expr.
             imp_sie_eval_expr
               (imp_sie_compose get (rho s) (sigma s))
               e2
               (ImpSieEnormal
                  (imp_sie_interp_symbolic_expr (rho s) o1)) /\
             (!v.
                v IN imp_sie_vars_in_symbolic_expr o1 ==>
                ?x. get (sigma s) x = SOME v)
             ==>
             (case e of
                ImpSieElit n => F
              | ImpSieEvar x => F
              | ImpSieEsub f f1 => f = e1 \/ f1 = e1) /\
             (!o2 : 'svar imp_sie_symbolic_expr.
                imp_sie_eval_expr
                  (imp_sie_compose get (rho s) (sigma s))
                  e1
                  (ImpSieEnormal
                     (imp_sie_interp_symbolic_expr (rho s) o2)) /\
                (!v.
                   v IN imp_sie_vars_in_symbolic_expr o2 ==>
                   ?x. get (sigma s) x = SOME v)
                ==>
                (let result : 'svar imp_sie_symbolic_expr =
                       ImpSieSsub o2 o1
                 in
                   imp_sie_eval_expr
                     (imp_sie_compose get (rho s) (sigma s))
                     e
                     (ImpSieEnormal
                        (imp_sie_interp_symbolic_expr (rho s) result)) /\
                   !v.
                     v IN imp_sie_vars_in_symbolic_expr result ==>
                     ?x. get (sigma s) x = SOME v)) /\
             (imp_sie_eval_expr
                (imp_sie_compose get (rho s) (sigma s))
                e1
                ImpSieEunboundVar
              ==>
              imp_sie_eval_expr
                (imp_sie_compose get (rho s) (sigma s))
                e
                ImpSieEunboundVar)) /\
          (imp_sie_eval_expr
             (imp_sie_compose get (rho s) (sigma s))
             e2
             ImpSieEunboundVar
           ==>
           imp_sie_eval_expr
             (imp_sie_compose get (rho s) (sigma s))
             e
             ImpSieEunboundVar)``;
