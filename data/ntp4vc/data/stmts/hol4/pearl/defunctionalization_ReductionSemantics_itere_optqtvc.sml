(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_itere_optqtvc: a
  reduction-semantics iteration verification condition relating context
  recomposition, redex and value recognition, and preservation of direct
  expression evaluation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  itere_opt_expr =
    ItereOptCte int
  | ItereOptSub itere_opt_expr itere_opt_expr
End

val itere_opt_eval_def = Define `
  (itere_opt_eval (ItereOptCte n) = n) /\
  (itere_opt_eval (ItereOptSub e1 e2) =
     itere_opt_eval e1 - itere_opt_eval e2)`;

val itere_opt_size_e_def = Define `
  (itere_opt_size_e (ItereOptCte x) = (1 : int)) /\
  (itere_opt_size_e (ItereOptSub e1 e2) =
     (3 : int) + itere_opt_size_e e1 + itere_opt_size_e e2)`;

Datatype:
  itere_opt_context =
    ItereOptEmpty
  | ItereOptLeft itere_opt_context itere_opt_expr
  | ItereOptRight int itere_opt_context
End

val itere_opt_recompose_def = Define `
  (itere_opt_recompose ItereOptEmpty e = e) /\
  (itere_opt_recompose (ItereOptLeft c1 e2) e =
     itere_opt_recompose c1 (ItereOptSub e e2)) /\
  (itere_opt_recompose (ItereOptRight n1 c1) e =
     itere_opt_recompose c1 (ItereOptSub (ItereOptCte n1) e))`;

val itere_opt_is_a_redex_def = Define `
  itere_opt_is_a_redex e <=>
    ?n1 n2 : int.
      e = ItereOptSub (ItereOptCte n1) (ItereOptCte n2)`;

val itere_opt_is_a_value_def = Define `
  itere_opt_is_a_value e <=>
    ?n : int. e = ItereOptCte n`;

val itere_opt_is_empty_context_def = Define `
  itere_opt_is_empty_context c <=>
    c = ItereOptEmpty`;

val itere_opt_size_c_def = Define `
  (itere_opt_size_c ItereOptEmpty = (0 : int)) /\
  (itere_opt_size_c (ItereOptLeft c1 e) =
     (2 : int) + itere_opt_size_c c1 + itere_opt_size_e e) /\
  (itere_opt_size_c (ItereOptRight x c1) =
     (1 : int) + itere_opt_size_c c1)`;

val defunctionalization_ReductionSemantics_itere_opt_vc =
  ``!(c1 : itere_opt_context) (e : itere_opt_expr).
      ((!c : itere_opt_context.
         !r : itere_opt_expr.
           itere_opt_recompose c r = itere_opt_recompose c1 e /\
           itere_opt_is_a_redex r
           ==>
           itere_opt_is_a_redex r /\
           !o1 : itere_opt_expr.
             itere_opt_eval o1 = itere_opt_eval r
             ==>
             itere_opt_eval (itere_opt_recompose c o1) =
             itere_opt_eval (itere_opt_recompose c1 e)) /\
       (itere_opt_is_empty_context c1 /\
        itere_opt_is_a_value e
        ==>
        (case e of
           ItereOptCte n => T
         | ItereOptSub e1 e2 => F) /\
        !result : int.
          (case e of
             ItereOptCte n => result = n
           | ItereOptSub e1 e2 => F)
          ==>
          result =
            itere_opt_eval (itere_opt_recompose c1 e)))``;
