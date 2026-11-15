(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_decompose_termqtvc: a
  reduction-semantics term decomposition verification condition relating
  recomposition, redex and value recognition, and structural size decrease.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  decompose_term_expr =
    DecomposeTermCte int
  | DecomposeTermSub decompose_term_expr decompose_term_expr
End

val decompose_term_size_e_def = Define `
  (decompose_term_size_e (DecomposeTermCte x) = (1 : int)) /\
  (decompose_term_size_e (DecomposeTermSub e1 e2) =
     (3 : int) +
       decompose_term_size_e e1 +
       decompose_term_size_e e2)`;

Datatype:
  decompose_term_context =
    DecomposeTermEmpty
  | DecomposeTermLeft decompose_term_context decompose_term_expr
  | DecomposeTermRight int decompose_term_context
End

val decompose_term_recompose_def = Define `
  (decompose_term_recompose DecomposeTermEmpty e = e) /\
  (decompose_term_recompose (DecomposeTermLeft c1 e2) e =
     decompose_term_recompose c1 (DecomposeTermSub e e2)) /\
  (decompose_term_recompose (DecomposeTermRight n1 c1) e =
     decompose_term_recompose c1
       (DecomposeTermSub (DecomposeTermCte n1) e))`;

val decompose_term_is_a_redex_def = Define `
  decompose_term_is_a_redex e <=>
    ?n1 n2 : int.
      e =
        DecomposeTermSub
          (DecomposeTermCte n1)
          (DecomposeTermCte n2)`;

val decompose_term_is_a_value_def = Define `
  decompose_term_is_a_value e <=>
    ?n : int. e = DecomposeTermCte n`;

val decompose_term_is_empty_context_def = Define `
  decompose_term_is_empty_context c <=>
    c = DecomposeTermEmpty`;

val decompose_term_size_c_def = Define `
  (decompose_term_size_c DecomposeTermEmpty = (0 : int)) /\
  (decompose_term_size_c (DecomposeTermLeft c1 e) =
     (2 : int) +
       decompose_term_size_c c1 +
       decompose_term_size_e e) /\
  (decompose_term_size_c (DecomposeTermRight x c1) =
     (1 : int) + decompose_term_size_c c1)`;

val defunctionalization_ReductionSemantics_decompose_term_vc =
  ``!(e : decompose_term_expr) (c : decompose_term_context).
      case e of
        DecomposeTermCte n =>
          (((0 : int) <=
              decompose_term_size_e e + decompose_term_size_c c /\
            decompose_term_size_c c <
              decompose_term_size_e e + decompose_term_size_c c) /\
           (!c1 : decompose_term_context.
              !e1 : decompose_term_expr.
                decompose_term_recompose c1 e1 =
                  decompose_term_recompose c (DecomposeTermCte n) /\
                decompose_term_is_a_redex e1
                ==>
                decompose_term_recompose c1 e1 =
                  decompose_term_recompose c e /\
                decompose_term_is_a_redex e1) /\
           (decompose_term_is_empty_context c
            ==>
            decompose_term_is_empty_context c /\
            decompose_term_is_a_value e))
      | DecomposeTermSub e1 e2 =>
          let o1 = DecomposeTermLeft c e2
          in
            (((0 : int) <=
                decompose_term_size_e e + decompose_term_size_c c /\
              decompose_term_size_e e1 +
                decompose_term_size_c o1 <
              decompose_term_size_e e + decompose_term_size_c c) /\
             (!c1 : decompose_term_context.
                !e11 : decompose_term_expr.
                  decompose_term_recompose c1 e11 =
                    decompose_term_recompose o1 e1 /\
                  decompose_term_is_a_redex e11
                  ==>
                  decompose_term_recompose c1 e11 =
                    decompose_term_recompose c e /\
                  decompose_term_is_a_redex e11) /\
             (decompose_term_is_empty_context o1 /\
              decompose_term_is_a_value e1
              ==>
              decompose_term_is_empty_context c /\
              decompose_term_is_a_value e))``;
