(*
  Statement-only formalization of thousand-theorems corpus artifact Q1149458
  (thousand-theorems__isabelle__Q1149458), "Compactness theorem": a
  first-order theory is satisfiable if and only if every finite subtheory is
  satisfiable. This file contains no proof.
*)

theory Q1149458_compactness_theorem
  imports Main
begin

datatype 'f fo_term =
    FOVar nat
  | FOFunc 'f "'f fo_term list"

datatype ('f, 'r) fo_formula =
    FOFalse
  | FOEqual "'f fo_term" "'f fo_term"
  | FORel 'r "'f fo_term list"
  | FOImp "('f, 'r) fo_formula" "('f, 'r) fo_formula"
  | FOAll nat "('f, 'r) fo_formula"

type_synonym ('f, 'r) fo_universe = "('f + 'r) + nat"

record ('f, 'r) fo_structure =
  fo_carrier :: "('f, 'r) fo_universe set"
  fo_fun_interp ::
    "'f \<Rightarrow> ('f, 'r) fo_universe list \<Rightarrow> ('f, 'r) fo_universe"
  fo_rel_interp :: "'r \<Rightarrow> ('f, 'r) fo_universe list \<Rightarrow> bool"

primrec wf_fo_term :: "('f \<Rightarrow> nat) \<Rightarrow> 'f fo_term \<Rightarrow> bool" where
  "wf_fo_term ar (FOVar n) = True"
| "wf_fo_term ar (FOFunc f ts) =
    (length ts = ar f \<and> list_all (wf_fo_term ar) ts)"

primrec wf_fo_formula ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('r \<Rightarrow> nat) \<Rightarrow>
      ('f, 'r) fo_formula \<Rightarrow> bool" where
  "wf_fo_formula far rar FOFalse = True"
| "wf_fo_formula far rar (FOEqual s t) =
    (wf_fo_term far s \<and> wf_fo_term far t)"
| "wf_fo_formula far rar (FORel r ts) =
    (length ts = rar r \<and> list_all (wf_fo_term far) ts)"
| "wf_fo_formula far rar (FOImp p q) =
    (wf_fo_formula far rar p \<and> wf_fo_formula far rar q)"
| "wf_fo_formula far rar (FOAll n p) = wf_fo_formula far rar p"

primrec free_vars_fo_term :: "'f fo_term \<Rightarrow> nat list" where
  "free_vars_fo_term (FOVar n) = [n]"
| "free_vars_fo_term (FOFunc f ts) =
    concat (map free_vars_fo_term ts)"

primrec free_vars_fo_formula :: "('f, 'r) fo_formula \<Rightarrow> nat list" where
  "free_vars_fo_formula FOFalse = []"
| "free_vars_fo_formula (FOEqual s t) =
    (free_vars_fo_term s @ free_vars_fo_term t)"
| "free_vars_fo_formula (FORel r ts) =
    concat (map free_vars_fo_term ts)"
| "free_vars_fo_formula (FOImp p q) =
    (free_vars_fo_formula p @ free_vars_fo_formula q)"
| "free_vars_fo_formula (FOAll n p) =
    filter (\<lambda>m. m \<noteq> n) (free_vars_fo_formula p)"

definition is_fo_sentence ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('r \<Rightarrow> nat) \<Rightarrow>
      ('f, 'r) fo_formula \<Rightarrow> bool" where
  "is_fo_sentence far rar p \<longleftrightarrow>
    wf_fo_formula far rar p \<and> free_vars_fo_formula p = []"

definition fo_theory ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('r \<Rightarrow> nat) \<Rightarrow>
      ('f, 'r) fo_formula set \<Rightarrow> bool" where
  "fo_theory far rar T \<longleftrightarrow>
    (\<forall>p\<in>T. is_fo_sentence far rar p)"

definition wf_fo_structure ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'r) fo_structure \<Rightarrow> bool" where
  "wf_fo_structure far A \<longleftrightarrow>
    fo_carrier A \<noteq> {} \<and>
    (\<forall>f xs. length xs = far f \<longrightarrow>
      set xs \<subseteq> fo_carrier A \<longrightarrow>
      fo_fun_interp A f xs \<in> fo_carrier A)"

primrec eval_fo_term ::
    "('f, 'r) fo_structure \<Rightarrow>
      (nat \<Rightarrow> ('f, 'r) fo_universe) \<Rightarrow>
      'f fo_term \<Rightarrow> ('f, 'r) fo_universe" where
  "eval_fo_term A v (FOVar n) = v n"
| "eval_fo_term A v (FOFunc f ts) =
    fo_fun_interp A f (map (eval_fo_term A v) ts)"

primrec satisfies_fo ::
    "('f, 'r) fo_structure \<Rightarrow>
      (nat \<Rightarrow> ('f, 'r) fo_universe) \<Rightarrow>
      ('f, 'r) fo_formula \<Rightarrow> bool" where
  "satisfies_fo A v FOFalse = False"
| "satisfies_fo A v (FOEqual s t) =
    (eval_fo_term A v s = eval_fo_term A v t)"
| "satisfies_fo A v (FORel r ts) =
    fo_rel_interp A r (map (eval_fo_term A v) ts)"
| "satisfies_fo A v (FOImp p q) =
    (satisfies_fo A v p \<longrightarrow> satisfies_fo A v q)"
| "satisfies_fo A v (FOAll n p) =
    (\<forall>x\<in>fo_carrier A. satisfies_fo A (v(n := x)) p)"

definition fo_sentence_holds ::
    "('f, 'r) fo_structure \<Rightarrow> ('f, 'r) fo_formula \<Rightarrow> bool" where
  "fo_sentence_holds A p \<longleftrightarrow>
    (\<forall>v. range v \<subseteq> fo_carrier A \<longrightarrow> satisfies_fo A v p)"

definition fo_satisfiable ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('r \<Rightarrow> nat) \<Rightarrow>
      ('f, 'r) fo_formula set \<Rightarrow> bool" where
  "fo_satisfiable far rar T \<longleftrightarrow>
    (\<exists>A :: ('f, 'r) fo_structure.
      wf_fo_structure far A \<and> (\<forall>p\<in>T. fo_sentence_holds A p))"

definition fo_finitely_satisfiable ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('r \<Rightarrow> nat) \<Rightarrow>
      ('f, 'r) fo_formula set \<Rightarrow> bool" where
  "fo_finitely_satisfiable far rar T \<longleftrightarrow>
    (\<forall>T0. finite T0 \<longrightarrow> T0 \<subseteq> T \<longrightarrow>
      fo_satisfiable far rar T0)"

theorem compactness_theorem:
  fixes far :: "'f \<Rightarrow> nat"
    and rar :: "'r \<Rightarrow> nat"
    and T :: "('f, 'r) fo_formula set"
  assumes "fo_theory far rar T"
  shows "fo_satisfiable far rar T \<longleftrightarrow>
    fo_finitely_satisfiable far rar T"
  sorry

end
