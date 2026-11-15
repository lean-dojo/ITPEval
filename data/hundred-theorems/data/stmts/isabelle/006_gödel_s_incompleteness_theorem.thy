(*
  Statement-only formalization of Hundred Theorems artifact 006, "Gödel's
  Incompleteness Theorem": a weakly consistent theory extending the concrete
  arithmetic theory NN, with representable axiom membership, has a closed
  formula independent of the theory. This file contains no proof.
*)

theory Goedel_Incompleteness
  imports Main
begin

datatype arith_term =
    TVar nat
  | TZero
  | TSucc arith_term
  | TAdd arith_term arith_term
  | TMul arith_term arith_term

datatype arith_formula =
    FEq arith_term arith_term
  | FLt arith_term arith_term
  | FImp arith_formula arith_formula
  | FNeg arith_formula
  | FAll nat arith_formula

abbreviation FOr :: "arith_formula \<Rightarrow> arith_formula \<Rightarrow> arith_formula" where
  "FOr A B \<equiv> FImp (FNeg A) B"

abbreviation FAnd :: "arith_formula \<Rightarrow> arith_formula \<Rightarrow> arith_formula" where
  "FAnd A B \<equiv> FNeg (FImp A (FNeg B))"

abbreviation FIff :: "arith_formula \<Rightarrow> arith_formula \<Rightarrow> arith_formula" where
  "FIff A B \<equiv> FAnd (FImp A B) (FImp B A)"

abbreviation FEx :: "nat \<Rightarrow> arith_formula \<Rightarrow> arith_formula" where
  "FEx v A \<equiv> FNeg (FAll v (FNeg A))"

fun free_vars_term :: "arith_term \<Rightarrow> nat set" where
  "free_vars_term (TVar v) = {v}"
| "free_vars_term TZero = {}"
| "free_vars_term (TSucc t) = free_vars_term t"
| "free_vars_term (TAdd s t) = free_vars_term s \<union> free_vars_term t"
| "free_vars_term (TMul s t) = free_vars_term s \<union> free_vars_term t"

fun all_vars_term :: "arith_term \<Rightarrow> nat set" where
  "all_vars_term (TVar v) = {v}"
| "all_vars_term TZero = {}"
| "all_vars_term (TSucc t) = all_vars_term t"
| "all_vars_term (TAdd s t) = all_vars_term s \<union> all_vars_term t"
| "all_vars_term (TMul s t) = all_vars_term s \<union> all_vars_term t"

fun free_vars_formula :: "arith_formula \<Rightarrow> nat set" where
  "free_vars_formula (FEq s t) = free_vars_term s \<union> free_vars_term t"
| "free_vars_formula (FLt s t) = free_vars_term s \<union> free_vars_term t"
| "free_vars_formula (FImp A B) =
    free_vars_formula A \<union> free_vars_formula B"
| "free_vars_formula (FNeg A) = free_vars_formula A"
| "free_vars_formula (FAll v A) = free_vars_formula A - {v}"

fun all_vars_formula :: "arith_formula \<Rightarrow> nat set" where
  "all_vars_formula (FEq s t) = all_vars_term s \<union> all_vars_term t"
| "all_vars_formula (FLt s t) = all_vars_term s \<union> all_vars_term t"
| "all_vars_formula (FImp A B) =
    all_vars_formula A \<union> all_vars_formula B"
| "all_vars_formula (FNeg A) = all_vars_formula A"
| "all_vars_formula (FAll v A) = insert v (all_vars_formula A)"

fun rename_term :: "nat \<Rightarrow> nat \<Rightarrow> arith_term \<Rightarrow> arith_term" where
  "rename_term x y (TVar v) = TVar (if v = x then y else v)"
| "rename_term x y TZero = TZero"
| "rename_term x y (TSucc t) = TSucc (rename_term x y t)"
| "rename_term x y (TAdd s t) =
    TAdd (rename_term x y s) (rename_term x y t)"
| "rename_term x y (TMul s t) =
    TMul (rename_term x y s) (rename_term x y t)"

fun rename_bound ::
    "nat \<Rightarrow> nat \<Rightarrow> arith_formula \<Rightarrow> arith_formula" where
  "rename_bound x y (FEq s t) =
    FEq (rename_term x y s) (rename_term x y t)"
| "rename_bound x y (FLt s t) =
    FLt (rename_term x y s) (rename_term x y t)"
| "rename_bound x y (FImp A B) =
    FImp (rename_bound x y A) (rename_bound x y B)"
| "rename_bound x y (FNeg A) = FNeg (rename_bound x y A)"
| "rename_bound x y (FAll v A) =
    (if v = x then FAll v A else FAll v (rename_bound x y A))"

fun formula_depth :: "arith_formula \<Rightarrow> nat" where
  "formula_depth (FEq s t) = 1"
| "formula_depth (FLt s t) = 1"
| "formula_depth (FImp A B) =
    Suc (max (formula_depth A) (formula_depth B))"
| "formula_depth (FNeg A) = Suc (formula_depth A)"
| "formula_depth (FAll v A) = Suc (formula_depth A)"

fun subst_term ::
    "arith_term \<Rightarrow> nat \<Rightarrow> arith_term \<Rightarrow> arith_term" where
  "subst_term (TVar v) x s = (if v = x then s else TVar v)"
| "subst_term TZero x s = TZero"
| "subst_term (TSucc t) x s = TSucc (subst_term t x s)"
| "subst_term (TAdd t u) x s =
    TAdd (subst_term t x s) (subst_term u x s)"
| "subst_term (TMul t u) x s =
    TMul (subst_term t x s) (subst_term u x s)"

fun subst_formula_fuel ::
    "nat \<Rightarrow> arith_formula \<Rightarrow> nat \<Rightarrow> arith_term
      \<Rightarrow> arith_formula" where
  "subst_formula_fuel 0 A x s = A"
| "subst_formula_fuel (Suc n) (FEq t u) x s =
    FEq (subst_term t x s) (subst_term u x s)"
| "subst_formula_fuel (Suc n) (FLt t u) x s =
    FLt (subst_term t x s) (subst_term u x s)"
| "subst_formula_fuel (Suc n) (FImp A B) x s =
    FImp (subst_formula_fuel n A x s) (subst_formula_fuel n B x s)"
| "subst_formula_fuel (Suc n) (FNeg A) x s =
    FNeg (subst_formula_fuel n A x s)"
| "subst_formula_fuel (Suc n) (FAll v A) x s =
    (if v = x then FAll v A
     else if v \<in> free_vars_term s then
       (let fresh =
          Suc (Max (all_vars_formula A \<union> all_vars_term s \<union> {x, v}))
        in FAll fresh
          (subst_formula_fuel n (rename_bound v fresh A) x s))
     else FAll v (subst_formula_fuel n A x s))"

definition subst_formula ::
    "arith_formula \<Rightarrow> nat \<Rightarrow> arith_term \<Rightarrow> arith_formula" where
  "subst_formula A x s = subst_formula_fuel (formula_depth A) A x s"

fun numeral :: "nat \<Rightarrow> arith_term" where
  "numeral 0 = TZero"
| "numeral (Suc n) = TSucc (numeral n)"

definition pair_code :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_code a b = 2 ^ a * (2 * b + 1)"

fun code_term :: "arith_term \<Rightarrow> nat" where
  "code_term (TVar v) = 5 * v"
| "code_term TZero = 1"
| "code_term (TSucc t) = 5 * code_term t + 2"
| "code_term (TAdd s t) = 5 * pair_code (code_term s) (code_term t) + 3"
| "code_term (TMul s t) = 5 * pair_code (code_term s) (code_term t) + 4"

fun code_formula :: "arith_formula \<Rightarrow> nat" where
  "code_formula (FEq s t) = 5 * pair_code (code_term s) (code_term t)"
| "code_formula (FLt s t) =
    5 * pair_code (code_term s) (code_term t) + 1"
| "code_formula (FImp A B) =
    5 * pair_code (code_formula A) (code_formula B) + 2"
| "code_formula (FNeg A) = 5 * code_formula A + 3"
| "code_formula (FAll v A) =
    5 * pair_code v (code_formula A) + 4"

definition reflect :: "arith_formula \<Rightarrow> arith_term" where
  "reflect A = numeral (code_formula A)"

fun free_vars_context :: "arith_formula list \<Rightarrow> nat set" where
  "free_vars_context [] = {}"
| "free_vars_context (A # H) =
    free_vars_formula A \<union> free_vars_context H"

definition less_congruence :: arith_formula where
  "less_congruence =
    FImp (FEq (TVar 0) (TVar 1))
      (FImp (FEq (TVar 2) (TVar 3))
        (FIff (FLt (TVar 0) (TVar 2))
          (FLt (TVar 1) (TVar 3))))"

definition succ_congruence :: arith_formula where
  "succ_congruence =
    FImp (FEq (TVar 0) (TVar 1))
      (FEq (TSucc (TVar 0)) (TSucc (TVar 1)))"

definition add_congruence :: arith_formula where
  "add_congruence =
    FImp (FEq (TVar 0) (TVar 1))
      (FImp (FEq (TVar 2) (TVar 3))
        (FEq (TAdd (TVar 0) (TVar 2))
          (TAdd (TVar 1) (TVar 3))))"

definition mul_congruence :: arith_formula where
  "mul_congruence =
    FImp (FEq (TVar 0) (TVar 1))
      (FImp (FEq (TVar 2) (TVar 3))
        (FEq (TMul (TVar 0) (TVar 2))
          (TMul (TVar 1) (TVar 3))))"

inductive derivation :: "arith_formula list \<Rightarrow> arith_formula \<Rightarrow> bool" where
  D_axiom: "derivation [A] A"
| D_modus_ponens:
    "\<lbrakk>derivation H1 (FImp A B); derivation H2 A\<rbrakk> \<Longrightarrow>
      derivation (H1 @ H2) B"
| D_generalization:
    "\<lbrakk>v \<notin> free_vars_context H; derivation H A\<rbrakk> \<Longrightarrow>
      derivation H (FAll v A)"
| D_imp1: "derivation [] (FImp A (FImp B A))"
| D_imp2:
    "derivation []
      (FImp (FImp A (FImp B C)) (FImp (FImp A B) (FImp A C)))"
| D_contraposition:
    "derivation [] (FImp (FImp (FNeg A) (FNeg B)) (FImp B A))"
| D_forall_elim:
    "derivation [] (FImp (FAll v A) (subst_formula A v t))"
| D_forall_intro:
    "v \<notin> free_vars_formula A \<Longrightarrow>
      derivation [] (FImp A (FAll v A))"
| D_forall_imp:
    "derivation []
      (FImp (FAll v (FImp A B)) (FImp (FAll v A) (FAll v B)))"
| D_eq_refl: "derivation [] (FEq (TVar 0) (TVar 0))"
| D_eq_sym:
    "derivation []
      (FImp (FEq (TVar 0) (TVar 1)) (FEq (TVar 1) (TVar 0)))"
| D_eq_trans:
    "derivation []
      (FImp (FEq (TVar 0) (TVar 1))
        (FImp (FEq (TVar 1) (TVar 2)) (FEq (TVar 0) (TVar 2))))"
| D_less_congruence: "derivation [] less_congruence"
| D_zero_congruence: "derivation [] (FEq TZero TZero)"
| D_succ_congruence: "derivation [] succ_congruence"
| D_add_congruence: "derivation [] add_congruence"
| D_mul_congruence: "derivation [] mul_congruence"

definition provable ::
    "arith_formula set \<Rightarrow> arith_formula \<Rightarrow> bool" where
  "provable T A \<longleftrightarrow>
    (\<exists>H. derivation H A \<and> set H \<subseteq> T)"

definition nn1_axiom :: arith_formula where
  "nn1_axiom = FAll 0 (FNeg (FEq (TSucc (TVar 0)) TZero))"

definition nn2_axiom :: arith_formula where
  "nn2_axiom =
    FAll 1 (FAll 0
      (FImp (FEq (TSucc (TVar 0)) (TSucc (TVar 1)))
        (FEq (TVar 0) (TVar 1))))"

definition nn3_axiom :: arith_formula where
  "nn3_axiom = FAll 0 (FEq (TAdd (TVar 0) TZero) (TVar 0))"

definition nn4_axiom :: arith_formula where
  "nn4_axiom =
    FAll 1 (FAll 0
      (FEq (TAdd (TVar 0) (TSucc (TVar 1)))
        (TSucc (TAdd (TVar 0) (TVar 1)))))"

definition nn5_axiom :: arith_formula where
  "nn5_axiom = FAll 0 (FEq (TMul (TVar 0) TZero) TZero)"

definition nn6_axiom :: arith_formula where
  "nn6_axiom =
    FAll 1 (FAll 0
      (FEq (TMul (TVar 0) (TSucc (TVar 1)))
        (TAdd (TMul (TVar 0) (TVar 1)) (TVar 0))))"

definition nn7_axiom :: arith_formula where
  "nn7_axiom = FAll 0 (FNeg (FLt (TVar 0) TZero))"

definition nn8_axiom :: arith_formula where
  "nn8_axiom =
    FAll 1 (FAll 0
      (FImp (FLt (TVar 0) (TSucc (TVar 1)))
        (FOr (FLt (TVar 0) (TVar 1)) (FEq (TVar 0) (TVar 1)))))"

definition nn9_axiom :: arith_formula where
  "nn9_axiom =
    FAll 1 (FAll 0
      (FOr (FLt (TVar 0) (TVar 1))
        (FOr (FEq (TVar 0) (TVar 1)) (FLt (TVar 1) (TVar 0)))))"

definition NN :: "arith_formula set" where
  "NN =
    {nn1_axiom, nn2_axiom, nn3_axiom, nn4_axiom, nn5_axiom,
      nn6_axiom, nn7_axiom, nn8_axiom, nn9_axiom}"

definition weakly_consistent :: "arith_formula set \<Rightarrow> bool" where
  "weakly_consistent T \<longleftrightarrow>
    (\<forall>A v.
      (\<forall>x \<in> free_vars_formula A. v = x) \<longrightarrow>
      provable T (FEx v (FNeg A)) \<longrightarrow>
      (\<exists>n. \<not> provable T (subst_formula A v (numeral n))))"

definition independent ::
    "arith_formula set \<Rightarrow> arith_formula \<Rightarrow> bool" where
  "independent T A \<longleftrightarrow>
    (\<not> provable T A \<and> \<not> provable T (FNeg A))"

definition closed :: "arith_formula \<Rightarrow> bool" where
  "closed A \<longleftrightarrow> free_vars_formula A = {}"

theorem goedel_first_incompleteness:
  fixes T :: "arith_formula set"
    and repT :: arith_formula
    and v0 :: nat
  assumes extends_NN: "NN \<subseteq> T"
    and free_var_repT:
      "\<And>v. v \<in> free_vars_formula repT \<Longrightarrow> v = v0"
    and express_T_positive:
      "\<And>A. A \<in> T \<Longrightarrow>
        provable T (subst_formula repT v0 (reflect A))"
    and express_T_negative:
      "\<And>A. A \<notin> T \<Longrightarrow>
        provable T (FNeg (subst_formula repT v0 (reflect A)))"
    and omega_consistency: "weakly_consistent T"
  shows "\<exists>A. independent T A \<and> closed A"
  sorry

end
