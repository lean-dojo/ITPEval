(*
  Statement-only formalization of Hundred Theorems artifact 006,
  "Gödel's Incompleteness Theorem": a weakly consistent theory extending
  the concrete arithmetic theory NN, with axiom membership represented by
  a formula whose only possible free variable is v0, has a closed formula
  independent of the theory. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory pred_setTheory listTheory;

val _ = Datatype `
  gterm =
      GVar num
    | GZero
    | GSucc gterm
    | GAdd gterm gterm
    | GMul gterm gterm
`;

val _ = Datatype `
  gformula =
      GEq gterm gterm
    | GLt gterm gterm
    | GImp gformula gformula
    | GNeg gformula
    | GAll num gformula
`;

val g_or_def = Define `
  g_or A B = GImp (GNeg A) B
`;

val g_and_def = Define `
  g_and A B = GNeg (GImp A (GNeg B))
`;

val g_iff_def = Define `
  g_iff A B = g_and (GImp A B) (GImp B A)
`;

val g_ex_def = Define `
  g_ex v A = GNeg (GAll v (GNeg A))
`;

val g_free_vars_term_def = Define `
  (g_free_vars_term (GVar v) = {v}) /\
  (g_free_vars_term GZero = EMPTY) /\
  (g_free_vars_term (GSucc t) = g_free_vars_term t) /\
  (g_free_vars_term (GAdd s t) =
    g_free_vars_term s UNION g_free_vars_term t) /\
  (g_free_vars_term (GMul s t) =
    g_free_vars_term s UNION g_free_vars_term t)
`;

val g_free_vars_formula_def = Define `
  (g_free_vars_formula (GEq s t) =
    g_free_vars_term s UNION g_free_vars_term t) /\
  (g_free_vars_formula (GLt s t) =
    g_free_vars_term s UNION g_free_vars_term t) /\
  (g_free_vars_formula (GImp A B) =
    g_free_vars_formula A UNION g_free_vars_formula B) /\
  (g_free_vars_formula (GNeg A) = g_free_vars_formula A) /\
  (g_free_vars_formula (GAll v A) = g_free_vars_formula A DELETE v)
`;

val g_max_var_term_def = Define `
  (g_max_var_term (GVar v) = v) /\
  (g_max_var_term GZero = 0) /\
  (g_max_var_term (GSucc t) = g_max_var_term t) /\
  (g_max_var_term (GAdd s t) =
    MAX (g_max_var_term s) (g_max_var_term t)) /\
  (g_max_var_term (GMul s t) =
    MAX (g_max_var_term s) (g_max_var_term t))
`;

val g_max_var_formula_def = Define `
  (g_max_var_formula (GEq s t) =
    MAX (g_max_var_term s) (g_max_var_term t)) /\
  (g_max_var_formula (GLt s t) =
    MAX (g_max_var_term s) (g_max_var_term t)) /\
  (g_max_var_formula (GImp A B) =
    MAX (g_max_var_formula A) (g_max_var_formula B)) /\
  (g_max_var_formula (GNeg A) = g_max_var_formula A) /\
  (g_max_var_formula (GAll v A) = MAX v (g_max_var_formula A))
`;

val g_rename_term_def = Define `
  (g_rename_term x y (GVar v) = GVar (if v = x then y else v)) /\
  (g_rename_term x y GZero = GZero) /\
  (g_rename_term x y (GSucc t) = GSucc (g_rename_term x y t)) /\
  (g_rename_term x y (GAdd s t) =
    GAdd (g_rename_term x y s) (g_rename_term x y t)) /\
  (g_rename_term x y (GMul s t) =
    GMul (g_rename_term x y s) (g_rename_term x y t))
`;

val g_rename_bound_def = Define `
  (g_rename_bound x y (GEq s t) =
    GEq (g_rename_term x y s) (g_rename_term x y t)) /\
  (g_rename_bound x y (GLt s t) =
    GLt (g_rename_term x y s) (g_rename_term x y t)) /\
  (g_rename_bound x y (GImp A B) =
    GImp (g_rename_bound x y A) (g_rename_bound x y B)) /\
  (g_rename_bound x y (GNeg A) = GNeg (g_rename_bound x y A)) /\
  (g_rename_bound x y (GAll v A) =
    if v = x then GAll v A else GAll v (g_rename_bound x y A))
`;

val g_formula_depth_def = Define `
  (g_formula_depth (GEq s t) = 1) /\
  (g_formula_depth (GLt s t) = 1) /\
  (g_formula_depth (GImp A B) =
    SUC (MAX (g_formula_depth A) (g_formula_depth B))) /\
  (g_formula_depth (GNeg A) = SUC (g_formula_depth A)) /\
  (g_formula_depth (GAll v A) = SUC (g_formula_depth A))
`;

val g_subst_term_def = Define `
  (g_subst_term (GVar v) x s = if v = x then s else GVar v) /\
  (g_subst_term GZero x s = GZero) /\
  (g_subst_term (GSucc t) x s = GSucc (g_subst_term t x s)) /\
  (g_subst_term (GAdd t u) x s =
    GAdd (g_subst_term t x s) (g_subst_term u x s)) /\
  (g_subst_term (GMul t u) x s =
    GMul (g_subst_term t x s) (g_subst_term u x s))
`;

val g_subst_formula_fuel_def = Define `
  (g_subst_formula_fuel 0 A x s = A) /\
  (g_subst_formula_fuel (SUC n) (GEq t u) x s =
    GEq (g_subst_term t x s) (g_subst_term u x s)) /\
  (g_subst_formula_fuel (SUC n) (GLt t u) x s =
    GLt (g_subst_term t x s) (g_subst_term u x s)) /\
  (g_subst_formula_fuel (SUC n) (GImp A B) x s =
    GImp (g_subst_formula_fuel n A x s)
         (g_subst_formula_fuel n B x s)) /\
  (g_subst_formula_fuel (SUC n) (GNeg A) x s =
    GNeg (g_subst_formula_fuel n A x s)) /\
  (g_subst_formula_fuel (SUC n) (GAll v A) x s =
    if v = x then GAll v A
    else if v IN g_free_vars_term s then
      let fresh =
        SUC (MAX (g_max_var_formula A)
                 (MAX (g_max_var_term s) (MAX x v)))
      in
        GAll fresh
          (g_subst_formula_fuel n (g_rename_bound v fresh A) x s)
    else
      GAll v (g_subst_formula_fuel n A x s))
`;

val g_subst_formula_def = Define `
  g_subst_formula A x s =
    g_subst_formula_fuel (g_formula_depth A) A x s
`;

val g_numeral_def = Define `
  (g_numeral 0 = GZero) /\
  (g_numeral (SUC n) = GSucc (g_numeral n))
`;

val g_pair_code_def = Define `
  g_pair_code a b = 2 ** a * (2 * b + 1)
`;

val g_code_term_def = Define `
  (g_code_term (GVar v) = 5 * v) /\
  (g_code_term GZero = 1) /\
  (g_code_term (GSucc t) = 5 * g_code_term t + 2) /\
  (g_code_term (GAdd s t) =
    5 * g_pair_code (g_code_term s) (g_code_term t) + 3) /\
  (g_code_term (GMul s t) =
    5 * g_pair_code (g_code_term s) (g_code_term t) + 4)
`;

val g_code_formula_def = Define `
  (g_code_formula (GEq s t) =
    5 * g_pair_code (g_code_term s) (g_code_term t)) /\
  (g_code_formula (GLt s t) =
    5 * g_pair_code (g_code_term s) (g_code_term t) + 1) /\
  (g_code_formula (GImp A B) =
    5 * g_pair_code (g_code_formula A) (g_code_formula B) + 2) /\
  (g_code_formula (GNeg A) = 5 * g_code_formula A + 3) /\
  (g_code_formula (GAll v A) =
    5 * g_pair_code v (g_code_formula A) + 4)
`;

val g_reflect_def = Define `
  g_reflect A = g_numeral (g_code_formula A)
`;

val g_free_vars_context_def = Define `
  (g_free_vars_context [] = EMPTY) /\
  (g_free_vars_context (A::H) =
    g_free_vars_formula A UNION g_free_vars_context H)
`;

val g_less_congruence_def = Define `
  g_less_congruence =
    GImp (GEq (GVar 0) (GVar 1))
      (GImp (GEq (GVar 2) (GVar 3))
        (g_iff (GLt (GVar 0) (GVar 2))
               (GLt (GVar 1) (GVar 3))))
`;

val g_succ_congruence_def = Define `
  g_succ_congruence =
    GImp (GEq (GVar 0) (GVar 1))
      (GEq (GSucc (GVar 0)) (GSucc (GVar 1)))
`;

val g_add_congruence_def = Define `
  g_add_congruence =
    GImp (GEq (GVar 0) (GVar 1))
      (GImp (GEq (GVar 2) (GVar 3))
        (GEq (GAdd (GVar 0) (GVar 2))
             (GAdd (GVar 1) (GVar 3))))
`;

val g_mul_congruence_def = Define `
  g_mul_congruence =
    GImp (GEq (GVar 0) (GVar 1))
      (GImp (GEq (GVar 2) (GVar 3))
        (GEq (GMul (GVar 0) (GVar 2))
             (GMul (GVar 1) (GVar 3))))
`;

val _ = Datatype `
  gderivation =
      GDAxiom gformula
    | GDModusPonens gformula gformula gderivation gderivation
    | GDGeneralization num gderivation
    | GDImp1 gformula gformula
    | GDImp2 gformula gformula gformula
    | GDContraposition gformula gformula
    | GDForallElim num gformula gterm
    | GDForallIntro num gformula
    | GDForallImp num gformula gformula
    | GDEqRefl
    | GDEqSym
    | GDEqTrans
    | GDLessCongruence
    | GDZeroCongruence
    | GDSuccCongruence
    | GDAddCongruence
    | GDMulCongruence
`;

val g_derivation_context_def = Define `
  (g_derivation_context (GDAxiom A) = [A]) /\
  (g_derivation_context (GDModusPonens A B d1 d2) =
    g_derivation_context d1 ++ g_derivation_context d2) /\
  (g_derivation_context (GDGeneralization v d) =
    g_derivation_context d) /\
  (g_derivation_context (GDImp1 A B) = []) /\
  (g_derivation_context (GDImp2 A B C) = []) /\
  (g_derivation_context (GDContraposition A B) = []) /\
  (g_derivation_context (GDForallElim v A t) = []) /\
  (g_derivation_context (GDForallIntro v A) = []) /\
  (g_derivation_context (GDForallImp v A B) = []) /\
  (g_derivation_context GDEqRefl = []) /\
  (g_derivation_context GDEqSym = []) /\
  (g_derivation_context GDEqTrans = []) /\
  (g_derivation_context GDLessCongruence = []) /\
  (g_derivation_context GDZeroCongruence = []) /\
  (g_derivation_context GDSuccCongruence = []) /\
  (g_derivation_context GDAddCongruence = []) /\
  (g_derivation_context GDMulCongruence = [])
`;

val g_derivation_conclusion_def = Define `
  (g_derivation_conclusion (GDAxiom A) = A) /\
  (g_derivation_conclusion (GDModusPonens A B d1 d2) = B) /\
  (g_derivation_conclusion (GDGeneralization v d) =
    GAll v (g_derivation_conclusion d)) /\
  (g_derivation_conclusion (GDImp1 A B) = GImp A (GImp B A)) /\
  (g_derivation_conclusion (GDImp2 A B C) =
    GImp (GImp A (GImp B C)) (GImp (GImp A B) (GImp A C))) /\
  (g_derivation_conclusion (GDContraposition A B) =
    GImp (GImp (GNeg A) (GNeg B)) (GImp B A)) /\
  (g_derivation_conclusion (GDForallElim v A t) =
    GImp (GAll v A) (g_subst_formula A v t)) /\
  (g_derivation_conclusion (GDForallIntro v A) =
    GImp A (GAll v A)) /\
  (g_derivation_conclusion (GDForallImp v A B) =
    GImp (GAll v (GImp A B)) (GImp (GAll v A) (GAll v B))) /\
  (g_derivation_conclusion GDEqRefl = GEq (GVar 0) (GVar 0)) /\
  (g_derivation_conclusion GDEqSym =
    GImp (GEq (GVar 0) (GVar 1)) (GEq (GVar 1) (GVar 0))) /\
  (g_derivation_conclusion GDEqTrans =
    GImp (GEq (GVar 0) (GVar 1))
      (GImp (GEq (GVar 1) (GVar 2)) (GEq (GVar 0) (GVar 2)))) /\
  (g_derivation_conclusion GDLessCongruence = g_less_congruence) /\
  (g_derivation_conclusion GDZeroCongruence = GEq GZero GZero) /\
  (g_derivation_conclusion GDSuccCongruence = g_succ_congruence) /\
  (g_derivation_conclusion GDAddCongruence = g_add_congruence) /\
  (g_derivation_conclusion GDMulCongruence = g_mul_congruence)
`;

val g_valid_derivation_def = Define `
  (g_valid_derivation (GDAxiom A) = T) /\
  (g_valid_derivation (GDModusPonens A B d1 d2) =
    (g_valid_derivation d1 /\
     g_valid_derivation d2 /\
     (g_derivation_conclusion d1 = GImp A B) /\
     (g_derivation_conclusion d2 = A))) /\
  (g_valid_derivation (GDGeneralization v d) =
    (g_valid_derivation d /\
     v NOTIN g_free_vars_context (g_derivation_context d))) /\
  (g_valid_derivation (GDImp1 A B) = T) /\
  (g_valid_derivation (GDImp2 A B C) = T) /\
  (g_valid_derivation (GDContraposition A B) = T) /\
  (g_valid_derivation (GDForallElim v A t) = T) /\
  (g_valid_derivation (GDForallIntro v A) =
    (v NOTIN g_free_vars_formula A)) /\
  (g_valid_derivation (GDForallImp v A B) = T) /\
  (g_valid_derivation GDEqRefl = T) /\
  (g_valid_derivation GDEqSym = T) /\
  (g_valid_derivation GDEqTrans = T) /\
  (g_valid_derivation GDLessCongruence = T) /\
  (g_valid_derivation GDZeroCongruence = T) /\
  (g_valid_derivation GDSuccCongruence = T) /\
  (g_valid_derivation GDAddCongruence = T) /\
  (g_valid_derivation GDMulCongruence = T)
`;

val g_provable_def = Define `
  g_provable thy A <=>
    ?d. g_valid_derivation d /\
        g_derivation_conclusion d = A /\
        EVERY thy (g_derivation_context d)
`;

val g_nn1_axiom_def = Define `
  g_nn1_axiom = GAll 0 (GNeg (GEq (GSucc (GVar 0)) GZero))
`;

val g_nn2_axiom_def = Define `
  g_nn2_axiom =
    GAll 1 (GAll 0
      (GImp (GEq (GSucc (GVar 0)) (GSucc (GVar 1)))
            (GEq (GVar 0) (GVar 1))))
`;

val g_nn3_axiom_def = Define `
  g_nn3_axiom = GAll 0 (GEq (GAdd (GVar 0) GZero) (GVar 0))
`;

val g_nn4_axiom_def = Define `
  g_nn4_axiom =
    GAll 1 (GAll 0
      (GEq (GAdd (GVar 0) (GSucc (GVar 1)))
           (GSucc (GAdd (GVar 0) (GVar 1)))))
`;

val g_nn5_axiom_def = Define `
  g_nn5_axiom = GAll 0 (GEq (GMul (GVar 0) GZero) GZero)
`;

val g_nn6_axiom_def = Define `
  g_nn6_axiom =
    GAll 1 (GAll 0
      (GEq (GMul (GVar 0) (GSucc (GVar 1)))
           (GAdd (GMul (GVar 0) (GVar 1)) (GVar 0))))
`;

val g_nn7_axiom_def = Define `
  g_nn7_axiom = GAll 0 (GNeg (GLt (GVar 0) GZero))
`;

val g_nn8_axiom_def = Define `
  g_nn8_axiom =
    GAll 1 (GAll 0
      (GImp (GLt (GVar 0) (GSucc (GVar 1)))
        (g_or (GLt (GVar 0) (GVar 1))
              (GEq (GVar 0) (GVar 1)))))
`;

val g_nn9_axiom_def = Define `
  g_nn9_axiom =
    GAll 1 (GAll 0
      (g_or (GLt (GVar 0) (GVar 1))
        (g_or (GEq (GVar 0) (GVar 1))
              (GLt (GVar 1) (GVar 0)))))
`;

val g_NN_def = Define `
  g_NN =
    {g_nn1_axiom; g_nn2_axiom; g_nn3_axiom; g_nn4_axiom;
     g_nn5_axiom; g_nn6_axiom; g_nn7_axiom; g_nn8_axiom;
     g_nn9_axiom}
`;

val g_weakly_consistent_def = Define `
  g_weakly_consistent thy <=>
    !A v.
      (!x. x IN g_free_vars_formula A ==> v = x) ==>
      g_provable thy (g_ex v (GNeg A)) ==>
      ?n. ~g_provable thy (g_subst_formula A v (g_numeral n))
`;

val g_independent_def = Define `
  g_independent thy A <=>
    ~g_provable thy A /\ ~g_provable thy (GNeg A)
`;

val g_closed_def = Define `
  g_closed A <=> g_free_vars_formula A = EMPTY
`;

val goedel_first_incompleteness =
  ``!(thy : gformula -> bool) repT v0.
      g_NN SUBSET thy /\
      (!v. v IN g_free_vars_formula repT ==> v = v0) /\
      (!A. A IN thy ==>
        g_provable thy (g_subst_formula repT v0 (g_reflect A))) /\
      (!A. ~(A IN thy) ==>
        g_provable thy (GNeg (g_subst_formula repT v0 (g_reflect A)))) /\
      g_weakly_consistent thy
      ==>
      ?A. g_independent thy A /\ g_closed A``;
