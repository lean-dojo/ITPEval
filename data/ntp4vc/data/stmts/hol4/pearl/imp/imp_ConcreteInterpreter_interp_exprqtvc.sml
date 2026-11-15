(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/imp/imp_ConcreteInterpreter_interp_exprqtvc: an expression
  interpreter verification condition for literals, variable lookup,
  subtraction, and unbound-variable error propagation. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory;

Datatype:
  ici_expr =
    IciElit int
  | IciEvar 'var
  | IciEsub ici_expr ici_expr
End

Datatype:
  ici_expr_behaviour =
    IciEnormal int
  | IciEunboundVar
End

val (ici_eval_expr_rules,
     ici_eval_expr_ind,
     ici_eval_expr_cases) =
  Hol_reln `
    (!env n.
       ici_eval_expr env (IciElit n) (IciEnormal n)) /\
    (!env x n.
       env x = SOME n ==>
       ici_eval_expr env (IciEvar x) (IciEnormal n)) /\
    (!env x.
       env x = NONE ==>
       ici_eval_expr env (IciEvar x) IciEunboundVar) /\
    (!env e1 n1 e2 n2.
       ici_eval_expr env e1 (IciEnormal n1) /\
       ici_eval_expr env e2 (IciEnormal n2) ==>
       ici_eval_expr env (IciEsub e1 e2) (IciEnormal (n1 - n2))) /\
    (!env e1 e2.
       ici_eval_expr env e1 IciEunboundVar ==>
       ici_eval_expr env (IciEsub e1 e2) IciEunboundVar) /\
    (!env e1 n1 e2.
       ici_eval_expr env e1 (IciEnormal n1) /\
       ici_eval_expr env e2 IciEunboundVar ==>
       ici_eval_expr env (IciEsub e1 e2) IciEunboundVar)
  `;

val imp_ConcreteInterpreter_interp_expr_vc =
  ``!(model1 : 'env -> 'var -> int option)
      (e : 'var ici_expr)
      (env1 : 'env).
      case e of
        IciElit n =>
          ici_eval_expr (model1 env1) e (IciEnormal n)
      | IciEvar x =>
          (!result : int.
             (case model1 env1 x of
                NONE => F
              | SOME v => result = v) ==>
             ici_eval_expr
               (model1 env1) e (IciEnormal result)) /\
          (model1 env1 x = NONE ==>
           ici_eval_expr (model1 env1) e IciEunboundVar)
      | IciEsub e1 e2 =>
          (case e of
             IciElit n => F
           | IciEvar x => F
           | IciEsub f f1 => f = e2 \/ f1 = e2) /\
          (!o1 : int.
             ici_eval_expr (model1 env1) e2 (IciEnormal o1) ==>
             (case e of
                IciElit n => F
              | IciEvar x => F
              | IciEsub f f1 => f = e1 \/ f1 = e1) /\
             (!o2 : int.
                ici_eval_expr (model1 env1) e1 (IciEnormal o2) ==>
                ici_eval_expr
                  (model1 env1) e (IciEnormal (o2 - o1))) /\
             (ici_eval_expr (model1 env1) e1 IciEunboundVar ==>
              ici_eval_expr (model1 env1) e IciEunboundVar)) /\
          (ici_eval_expr (model1 env1) e2 IciEunboundVar ==>
           ici_eval_expr (model1 env1) e IciEunboundVar)``;
