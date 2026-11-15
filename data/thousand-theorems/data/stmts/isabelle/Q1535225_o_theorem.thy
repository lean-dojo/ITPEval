(*
  Statement-only formalization of thousand-theorems corpus artifact Q1535225,
  "Łoś' theorem": a first-order sentence holds in an ultraproduct exactly
  when it holds in almost every factor with respect to the ultrafilter.
  This file contains no proof.
*)

theory Q1535225_o_theorem
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

record ('f, 'r, 'a) fo_structure =
  fo_carrier :: "'a set"
  fo_fun_interp :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
  fo_rel_interp :: "'r \<Rightarrow> 'a list \<Rightarrow> bool"

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

definition wf_fo_structure ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'r, 'a) fo_structure \<Rightarrow> bool" where
  "wf_fo_structure far A \<longleftrightarrow>
    fo_carrier A \<noteq> {} \<and>
    (\<forall>f xs. length xs = far f \<longrightarrow>
      set xs \<subseteq> fo_carrier A \<longrightarrow>
      fo_fun_interp A f xs \<in> fo_carrier A)"

primrec eval_fo_term ::
    "('f, 'r, 'a) fo_structure \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
      'f fo_term \<Rightarrow> 'a" where
  "eval_fo_term A v (FOVar n) = v n"
| "eval_fo_term A v (FOFunc f ts) =
    fo_fun_interp A f (map (eval_fo_term A v) ts)"

primrec satisfies_fo ::
    "('f, 'r, 'a) fo_structure \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
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
    "('f, 'r, 'a) fo_structure \<Rightarrow> ('f, 'r) fo_formula \<Rightarrow> bool" where
  "fo_sentence_holds A p \<longleftrightarrow>
    (\<forall>v. range v \<subseteq> fo_carrier A \<longrightarrow> satisfies_fo A v p)"

definition los_ultrafilter :: "'i set set \<Rightarrow> bool" where
  "los_ultrafilter U \<longleftrightarrow>
    UNIV \<in> U \<and>
    {} \<notin> U \<and>
    (\<forall>A\<in>U. \<forall>B\<in>U. A \<inter> B \<in> U) \<and>
    (\<forall>A B. A \<in> U \<longrightarrow> A \<subseteq> B \<longrightarrow> B \<in> U) \<and>
    (\<forall>A. A \<in> U \<or> - A \<in> U)"

definition los_class ::
    "'i set set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "los_class U f = {g. {i. g i = f i} \<in> U}"

definition los_representative ::
    "'i set set \<Rightarrow> ('i \<Rightarrow> 'a) set \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "los_representative U X = (SOME f. los_class U f = X)"

definition los_product_carrier ::
    "'i set set \<Rightarrow> ('i \<Rightarrow> ('f, 'r, 'a) fo_structure) \<Rightarrow>
      ('i \<Rightarrow> 'a) set set" where
  "los_product_carrier U M =
    {los_class U f | f. \<forall>i. f i \<in> fo_carrier (M i)}"

definition fo_ultraproduct ::
    "'i set set \<Rightarrow> ('i \<Rightarrow> ('f, 'r, 'a) fo_structure) \<Rightarrow>
      ('f, 'r, ('i \<Rightarrow> 'a) set) fo_structure" where
  "fo_ultraproduct U M =
    \<lparr>fo_carrier = los_product_carrier U M,
      fo_fun_interp = (\<lambda>f Xs.
        los_class U (\<lambda>i.
          fo_fun_interp (M i) f
            (map (\<lambda>X. los_representative U X i) Xs))),
      fo_rel_interp = (\<lambda>r Xs.
        {i. fo_rel_interp (M i) r
          (map (\<lambda>X. los_representative U X i) Xs)} \<in> U)\<rparr>"

theorem los_theorem:
  fixes far :: "'f \<Rightarrow> nat"
    and rar :: "'r \<Rightarrow> nat"
    and U :: "'i set set"
    and M :: "'i \<Rightarrow> ('f, 'r, 'a) fo_structure"
    and p :: "('f, 'r) fo_formula"
  assumes "los_ultrafilter U"
    and "\<forall>i. wf_fo_structure far (M i)"
    and "is_fo_sentence far rar p"
  shows "fo_sentence_holds (fo_ultraproduct U M) p \<longleftrightarrow>
    {i. fo_sentence_holds (M i) p} \<in> U"
  sorry

end
