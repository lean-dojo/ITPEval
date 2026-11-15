(*
  Statement-only formalization of the thousand-theorems corpus artifact Q574902
  (thousand-theorems__isabelle__Q574902), "Tarski's indefinability theorem":
  no unary formula of first-order arithmetic defines truth for every arithmetic
  sentence in the standard natural-number model. This file contains no proof.
*)

theory Q574902_tarski_s_indefinability_theorem
  imports Main
begin

datatype q574902_term =
    Q574902_Var nat
  | Q574902_Zero
  | Q574902_One
  | Q574902_Add q574902_term q574902_term
  | Q574902_Mul q574902_term q574902_term

datatype q574902_formula =
    Q574902_False
  | Q574902_Eq q574902_term q574902_term
  | Q574902_Lt q574902_term q574902_term
  | Q574902_Imp q574902_formula q574902_formula
  | Q574902_Neg q574902_formula
  | Q574902_All nat q574902_formula

fun q574902_free_vars_term :: "q574902_term \<Rightarrow> nat set" where
  "q574902_free_vars_term (Q574902_Var v) = {v}"
| "q574902_free_vars_term Q574902_Zero = {}"
| "q574902_free_vars_term Q574902_One = {}"
| "q574902_free_vars_term (Q574902_Add s t) =
    q574902_free_vars_term s \<union> q574902_free_vars_term t"
| "q574902_free_vars_term (Q574902_Mul s t) =
    q574902_free_vars_term s \<union> q574902_free_vars_term t"

fun q574902_free_vars_formula :: "q574902_formula \<Rightarrow> nat set" where
  "q574902_free_vars_formula Q574902_False = {}"
| "q574902_free_vars_formula (Q574902_Eq s t) =
    q574902_free_vars_term s \<union> q574902_free_vars_term t"
| "q574902_free_vars_formula (Q574902_Lt s t) =
    q574902_free_vars_term s \<union> q574902_free_vars_term t"
| "q574902_free_vars_formula (Q574902_Imp A B) =
    q574902_free_vars_formula A \<union> q574902_free_vars_formula B"
| "q574902_free_vars_formula (Q574902_Neg A) =
    q574902_free_vars_formula A"
| "q574902_free_vars_formula (Q574902_All v A) =
    q574902_free_vars_formula A - {v}"

fun q574902_subst_term ::
    "q574902_term \<Rightarrow> nat \<Rightarrow> q574902_term \<Rightarrow> q574902_term" where
  "q574902_subst_term (Q574902_Var v) x s =
    (if v = x then s else Q574902_Var v)"
| "q574902_subst_term Q574902_Zero x s = Q574902_Zero"
| "q574902_subst_term Q574902_One x s = Q574902_One"
| "q574902_subst_term (Q574902_Add t u) x s =
    Q574902_Add (q574902_subst_term t x s) (q574902_subst_term u x s)"
| "q574902_subst_term (Q574902_Mul t u) x s =
    Q574902_Mul (q574902_subst_term t x s) (q574902_subst_term u x s)"

fun q574902_subst_closed ::
    "q574902_formula \<Rightarrow> nat \<Rightarrow> q574902_term \<Rightarrow>
      q574902_formula" where
  "q574902_subst_closed Q574902_False x s = Q574902_False"
| "q574902_subst_closed (Q574902_Eq t u) x s =
    Q574902_Eq (q574902_subst_term t x s) (q574902_subst_term u x s)"
| "q574902_subst_closed (Q574902_Lt t u) x s =
    Q574902_Lt (q574902_subst_term t x s) (q574902_subst_term u x s)"
| "q574902_subst_closed (Q574902_Imp A B) x s =
    Q574902_Imp (q574902_subst_closed A x s) (q574902_subst_closed B x s)"
| "q574902_subst_closed (Q574902_Neg A) x s =
    Q574902_Neg (q574902_subst_closed A x s)"
| "q574902_subst_closed (Q574902_All v A) x s =
    (if v = x then Q574902_All v A
     else Q574902_All v (q574902_subst_closed A x s))"

fun q574902_numeral :: "nat \<Rightarrow> q574902_term" where
  "q574902_numeral 0 = Q574902_Zero"
| "q574902_numeral (Suc n) = Q574902_Add Q574902_One (q574902_numeral n)"

definition q574902_pair_code :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q574902_pair_code a b = 2 ^ a * (2 * b + 1)"

fun q574902_code_term :: "q574902_term \<Rightarrow> nat" where
  "q574902_code_term (Q574902_Var v) = 6 * v"
| "q574902_code_term Q574902_Zero = 1"
| "q574902_code_term Q574902_One = 2"
| "q574902_code_term (Q574902_Add s t) =
    6 * q574902_pair_code (q574902_code_term s) (q574902_code_term t) + 3"
| "q574902_code_term (Q574902_Mul s t) =
    6 * q574902_pair_code (q574902_code_term s) (q574902_code_term t) + 4"

fun q574902_code_formula :: "q574902_formula \<Rightarrow> nat" where
  "q574902_code_formula Q574902_False = 0"
| "q574902_code_formula (Q574902_Eq s t) =
    6 * q574902_pair_code (q574902_code_term s) (q574902_code_term t) + 1"
| "q574902_code_formula (Q574902_Lt s t) =
    6 * q574902_pair_code (q574902_code_term s) (q574902_code_term t) + 2"
| "q574902_code_formula (Q574902_Imp A B) =
    6 * q574902_pair_code (q574902_code_formula A) (q574902_code_formula B) + 3"
| "q574902_code_formula (Q574902_Neg A) =
    6 * q574902_code_formula A + 4"
| "q574902_code_formula (Q574902_All v A) =
    6 * q574902_pair_code v (q574902_code_formula A) + 5"

fun q574902_eval_term ::
    "(nat \<Rightarrow> nat) \<Rightarrow> q574902_term \<Rightarrow> nat" where
  "q574902_eval_term e (Q574902_Var v) = e v"
| "q574902_eval_term e Q574902_Zero = 0"
| "q574902_eval_term e Q574902_One = 1"
| "q574902_eval_term e (Q574902_Add s t) =
    q574902_eval_term e s + q574902_eval_term e t"
| "q574902_eval_term e (Q574902_Mul s t) =
    q574902_eval_term e s * q574902_eval_term e t"

fun q574902_satisfies ::
    "(nat \<Rightarrow> nat) \<Rightarrow> q574902_formula \<Rightarrow> bool" where
  "q574902_satisfies e Q574902_False = False"
| "q574902_satisfies e (Q574902_Eq s t) =
    (q574902_eval_term e s = q574902_eval_term e t)"
| "q574902_satisfies e (Q574902_Lt s t) =
    (q574902_eval_term e s < q574902_eval_term e t)"
| "q574902_satisfies e (Q574902_Imp A B) =
    (q574902_satisfies e A \<longrightarrow> q574902_satisfies e B)"
| "q574902_satisfies e (Q574902_Neg A) = (\<not> q574902_satisfies e A)"
| "q574902_satisfies e (Q574902_All v A) =
    (\<forall>n. q574902_satisfies (e(v := n)) A)"

definition q574902_is_sentence :: "q574902_formula \<Rightarrow> bool" where
  "q574902_is_sentence A \<longleftrightarrow> q574902_free_vars_formula A = {}"

definition q574902_is_unary :: "q574902_formula \<Rightarrow> bool" where
  "q574902_is_unary A \<longleftrightarrow> q574902_free_vars_formula A \<subseteq> {0}"

definition q574902_true_in_nat :: "q574902_formula \<Rightarrow> bool" where
  "q574902_true_in_nat A \<longleftrightarrow> q574902_satisfies (\<lambda>_. 0) A"

theorem q574902_tarski_indefinability:
  "\<not> (\<exists>tau.
    q574902_is_unary tau \<and>
    (\<forall>sigma.
      q574902_is_sentence sigma \<longrightarrow>
      (q574902_true_in_nat sigma \<longleftrightarrow>
       q574902_true_in_nat
        (q574902_subst_closed tau 0
          (q574902_numeral (q574902_code_formula sigma))))))"
  sorry

end
