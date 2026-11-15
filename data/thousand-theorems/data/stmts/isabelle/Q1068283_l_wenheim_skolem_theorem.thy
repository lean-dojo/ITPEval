(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1068283 (thousand-theorems__isabelle__Q1068283), "Löwenheim–Skolem
  theorem": for an infinite first-order structure and any infinite cardinal
  at least the cardinality of its language, there is a structure of exactly
  that cardinality with an elementary embedding in the appropriate direction.
  This file contains no proof.
*)

theory Q1068283_l_wenheim_skolem_theorem
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
  fun_interp :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
  rel_interp :: "'r \<Rightarrow> 'a list \<Rightarrow> bool"

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

primrec eval_fo_term ::
    "('f, 'r, 'a) fo_structure \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
      'f fo_term \<Rightarrow> 'a" where
  "eval_fo_term A v (FOVar n) = v n"
| "eval_fo_term A v (FOFunc f ts) =
    fun_interp A f (map (eval_fo_term A v) ts)"

primrec satisfies_fo ::
    "('f, 'r, 'a) fo_structure \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
      ('f, 'r) fo_formula \<Rightarrow> bool" where
  "satisfies_fo A v FOFalse = False"
| "satisfies_fo A v (FOEqual s t) =
    (eval_fo_term A v s = eval_fo_term A v t)"
| "satisfies_fo A v (FORel r ts) =
    rel_interp A r (map (eval_fo_term A v) ts)"
| "satisfies_fo A v (FOImp p q) =
    (satisfies_fo A v p \<longrightarrow> satisfies_fo A v q)"
| "satisfies_fo A v (FOAll n p) =
    (\<forall>x. satisfies_fo A (v(n := x)) p)"

definition fo_elementary_embedding ::
    "('f \<Rightarrow> nat) \<Rightarrow> ('r \<Rightarrow> nat) \<Rightarrow>
      ('f, 'r, 'a) fo_structure \<Rightarrow>
      ('f, 'r, 'b) fo_structure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "fo_elementary_embedding far rar A B e \<longleftrightarrow>
    inj e \<and>
    (\<forall>p v. wf_fo_formula far rar p \<longrightarrow>
      (satisfies_fo A v p \<longleftrightarrow> satisfies_fo B (e \<circ> v) p))"

theorem lowenheim_skolem:
  fixes far :: "'f \<Rightarrow> nat"
    and rar :: "'r \<Rightarrow> nat"
    and M :: "('f, 'r, 'm) fo_structure"
  assumes "infinite (UNIV :: 'm set)"
    and "infinite (UNIV :: 'k set)"
    and "ordLeq3 (card_of (UNIV :: ('f + 'r) set))
      (card_of (UNIV :: 'k set))"
  shows "\<exists>N :: ('f, 'r, 'k) fo_structure.
    (\<exists>e :: 'k \<Rightarrow> 'm. fo_elementary_embedding far rar N M e) \<or>
    (\<exists>e :: 'm \<Rightarrow> 'k. fo_elementary_embedding far rar M N e)"
  sorry

end
