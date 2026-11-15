(*   Title: HOL/ex/Ballot.thy
     Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
     Author: Johannes Hölzl <hoelzl@in.tum.de>
*)

section \<open>Bertrand's Ballot Theorem\<close>

theory Ballot
imports
  Complex_Main
  "HOL-Library.FuncSet"
begin

subsection \<open>Preliminaries\<close>

lemma card_bij':
  assumes "f \<in> A \<rightarrow> B" "\<And>x. x \<in> A \<Longrightarrow> g (f x) = x"
    and "g \<in> B \<rightarrow> A" "\<And>x. x \<in> B \<Longrightarrow> f (g x) = x"
  shows "card A = card B"
  by sorry

subsection \<open>Formalization of Problem Statement\<close>

subsubsection \<open>Basic Definitions\<close>

datatype vote = A | B

definition
  "all_countings a b = card {f \<in> {1 .. a + b} \<rightarrow>\<^sub>E {A, B}.
      card {x \<in> {1 .. a + b}. f x = A} = a \<and> card {x \<in> {1 .. a + b}. f x = B} = b}"

definition
  "valid_countings a b =
    card {f\<in>{1..a+b} \<rightarrow>\<^sub>E {A, B}.
      card {x\<in>{1..a+b}. f x = A} = a \<and> card {x\<in>{1..a+b}. f x = B} = b \<and>
      (\<forall>m\<in>{1..a+b}. card {x\<in>{1..m}. f x = A} > card {x\<in>{1..m}. f x = B})}"

subsubsection \<open>Equivalence with Set Cardinality\<close>

lemma Collect_on_transfer:
  assumes "rel_set R X Y"
  shows "rel_fun (rel_fun R (=)) (rel_set R) (\<lambda>P. {x\<in>X. P x}) (\<lambda>P. {y\<in>Y. P y})"
  by sorry

lemma rel_fun_trans:
  "rel_fun P Q g g' \<Longrightarrow> rel_fun R P f f' \<Longrightarrow> rel_fun R Q (\<lambda>x. g (f x)) (\<lambda>y. g' (f' y))"
  by sorry

lemma rel_fun_trans2:
  "rel_fun P1 (rel_fun P2 Q) g g' \<Longrightarrow> rel_fun R P1 f1 f1' \<Longrightarrow> rel_fun R P2 f2 f2' \<Longrightarrow>
    rel_fun R Q (\<lambda>x. g (f1 x) (f2 x)) (\<lambda>y. g' (f1' y) (f2' y))"
  by sorry

lemma rel_fun_trans2':
  "rel_fun R (=) f1 f1' \<Longrightarrow> rel_fun R (=) f2 f2' \<Longrightarrow>
    rel_fun R (=) (\<lambda>x. g (f1 x) (f2 x)) (\<lambda>y. g (f1' y) (f2' y))"
  by sorry

lemma rel_fun_const: "rel_fun R (=) (\<lambda>x. a) (\<lambda>y. a)"
  by sorry

lemma rel_fun_conj:
  "rel_fun R (=) f f' \<Longrightarrow> rel_fun R (=) g g' \<Longrightarrow> rel_fun R (=) (\<lambda>x. f x \<and> g x) (\<lambda>y. f' y \<and> g' y)"
  by sorry

lemma rel_fun_ball:
  "(\<And>i. i \<in> I \<Longrightarrow> rel_fun R (=) (f i) (f' i)) \<Longrightarrow> rel_fun R (=) (\<lambda>x. \<forall>i\<in>I. f i x) (\<lambda>y. \<forall>i\<in>I. f' i y)"
  by sorry

lemma
  shows all_countings_set: "all_countings a b = card {V\<in>Pow {0..<a+b}. card V = a}"
      (is "_ = card ?A")
    and valid_countings_set: "valid_countings a b =
      card {V\<in>Pow {0..<a+b}. card V = a \<and> (\<forall>m\<in>{1..a+b}. card ({0..<m} \<inter> V) > m - card ({0..<m} \<inter> V))}"
      (is "_ = card ?V")
  by sorry

lemma all_countings [code]: "all_countings a b = (a + b) choose a"
  by sorry

subsection \<open>Facts About \<^term>\<open>valid_countings\<close>\<close>

subsubsection \<open>Non-Recursive Cases\<close>

lemma card_V_eq_a: "V \<subseteq> {0..<a} \<Longrightarrow> card V = a \<longleftrightarrow> V = {0..<a}"
  by sorry

lemma valid_countings_a_0: "valid_countings a 0 = 1"
  by sorry

lemma valid_countings_eq_zero:
  "a \<le> b \<Longrightarrow> 0 < b \<Longrightarrow> valid_countings a b = 0"
  by sorry

lemma Ico_subset_finite: "i \<subseteq> {a ..< b::nat} \<Longrightarrow> finite i"
  by sorry

lemma Icc_Suc2: "a \<le> b \<Longrightarrow> {a..Suc b} = insert (Suc b) {a..b}"
  by sorry

lemma Ico_Suc2: "a \<le> b \<Longrightarrow> {a..<Suc b} = insert b {a..<b}"
  by sorry

lemma valid_countings_Suc_Suc:
  assumes "b < a"
  shows "valid_countings (Suc a) (Suc b) = valid_countings a (Suc b) + valid_countings (Suc a) b"
  by sorry

lemma valid_countings:
  "(a + b) * valid_countings a b = (a - b) * ((a + b) choose a)"
  by sorry

lemma valid_countings_eq[code]:
  "valid_countings a b = (if a + b = 0 then 1 else ((a - b) * ((a + b) choose a)) div (a + b))"
  by sorry

subsection \<open>Relation Between \<^term>\<open>valid_countings\<close> and \<^term>\<open>all_countings\<close>\<close>

lemma main_nat: "(a + b) * valid_countings a b = (a - b) * all_countings a b"
  by sorry

lemma main_real:
  assumes "b < a"
  shows "valid_countings a b = (a - b) / (a + b) * all_countings a b"
  by sorry

lemma
  "valid_countings a b = (if a \<le> b then (if b = 0 then 1 else 0) else (a - b) / (a + b) * all_countings a b)"
  by sorry

subsubsection \<open>Executable Definition\<close>

value "all_countings 1 0"
value "all_countings 0 1"
value "all_countings 1 1"
value "all_countings 2 1"
value "all_countings 1 2"
value "all_countings 2 4"
value "all_countings 4 2"

subsubsection \<open>Executable Definition\<close>

value "valid_countings 1 0"
value "valid_countings 0 1"
value "valid_countings 1 1"
value "valid_countings 2 1"
value "valid_countings 1 2"
value "valid_countings 2 4"
value "valid_countings 4 2"

end
