(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_decompose_contqtvc: a
  reduction-semantics continuation decomposition verification condition
  relating recomposition, redex and value recognition, and structural size
  decrease. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  decompose_cont_expr =
    DecomposeContCte int
  | DecomposeContSub decompose_cont_expr decompose_cont_expr
End

val decompose_cont_size_e_def = Define `
  (decompose_cont_size_e (DecomposeContCte x) = (1 : int)) /\
  (decompose_cont_size_e (DecomposeContSub e1 e2) =
     (3 : int) +
       decompose_cont_size_e e1 +
       decompose_cont_size_e e2)`;

Datatype:
  decompose_cont_context =
    DecomposeContEmpty
  | DecomposeContLeft decompose_cont_context decompose_cont_expr
  | DecomposeContRight int decompose_cont_context
End

val decompose_cont_recompose_def = Define `
  (decompose_cont_recompose DecomposeContEmpty e = e) /\
  (decompose_cont_recompose (DecomposeContLeft c1 e2) e =
     decompose_cont_recompose c1 (DecomposeContSub e e2)) /\
  (decompose_cont_recompose (DecomposeContRight n1 c1) e =
     decompose_cont_recompose c1
       (DecomposeContSub (DecomposeContCte n1) e))`;

val decompose_cont_is_a_redex_def = Define `
  decompose_cont_is_a_redex e <=>
    ?n1 n2 : int.
      e =
        DecomposeContSub
          (DecomposeContCte n1)
          (DecomposeContCte n2)`;

val decompose_cont_is_a_value_def = Define `
  decompose_cont_is_a_value e <=>
    ?n : int. e = DecomposeContCte n`;

val decompose_cont_is_empty_context_def = Define `
  decompose_cont_is_empty_context c <=>
    c = DecomposeContEmpty`;

val decompose_cont_size_c_def = Define `
  (decompose_cont_size_c DecomposeContEmpty = (0 : int)) /\
  (decompose_cont_size_c (DecomposeContLeft c1 e) =
     (2 : int) +
       decompose_cont_size_c c1 +
       decompose_cont_size_e e) /\
  (decompose_cont_size_c (DecomposeContRight x c1) =
     (1 : int) + decompose_cont_size_c c1)`;

val defunctionalization_ReductionSemantics_decompose_cont_vc =
  ``!(c : decompose_cont_context) (n : int).
      case c of
        DecomposeContEmpty =>
          decompose_cont_is_empty_context c
      | DecomposeContLeft c1 e =>
          let o1 = DecomposeContRight n c1
          in
            (((0 : int) <= decompose_cont_size_c c /\
              decompose_cont_size_e e +
                decompose_cont_size_c o1 <
              decompose_cont_size_c c) /\
             (!c11 : decompose_cont_context.
                !e1 : decompose_cont_expr.
                  decompose_cont_recompose c11 e1 =
                    decompose_cont_recompose o1 e /\
                  decompose_cont_is_a_redex e1
                  ==>
                  decompose_cont_recompose c11 e1 =
                    decompose_cont_recompose c
                      (DecomposeContCte n) /\
                  decompose_cont_is_a_redex e1) /\
             (decompose_cont_is_empty_context o1 /\
              decompose_cont_is_a_value e
              ==>
              decompose_cont_is_empty_context c))
      | DecomposeContRight n1 c1 =>
          let o1 =
            DecomposeContSub
              (DecomposeContCte n1)
              (DecomposeContCte n)
          in
            decompose_cont_recompose c1 o1 =
              decompose_cont_recompose c (DecomposeContCte n) /\
            decompose_cont_is_a_redex o1``;
