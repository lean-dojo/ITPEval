(*   Title: HOL/ex/Erdős_Szekeres.thy
     Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
*)

section \<open>The Erdös-Szekeres Theorem\<close>

theory Erdoes_Szekeres
imports Main
begin

lemma exists_set_with_max_card:
  assumes "finite S" "S \<noteq> {}"
  shows "\<exists>s \<in> S. card s = Max (card ` S)"
  by sorry

subsection \<open>Definition of Monotonicity over a Carrier Set\<close>

definition
  "gen_mono_on f R S = (\<forall>i\<in>S. \<forall>j\<in>S. i \<le> j \<longrightarrow> R (f i) (f j))"

lemma gen_mono_on_empty [simp]: "gen_mono_on f R {}"
  by sorry

lemma gen_mono_on_singleton [simp]: "reflp R \<Longrightarrow> gen_mono_on f R {x}"
  by sorry

lemma gen_mono_on_subset: "T \<subseteq> S \<Longrightarrow> gen_mono_on f R S \<Longrightarrow> gen_mono_on f R T"
  by sorry

lemma not_gen_mono_on_subset: "T \<subseteq> S \<Longrightarrow> \<not> gen_mono_on f R T \<Longrightarrow> \<not> gen_mono_on f R S"
  by sorry

lemma [simp]:
  "reflp ((\<le>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  "reflp ((\<ge>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  "transp ((\<le>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  "transp ((\<ge>) :: 'a::order \<Rightarrow> _ \<Rightarrow> bool)"
  by sorry

subsection \<open>The Erdoes-Szekeres Theorem following Seidenberg's (1959) argument\<close>

lemma Erdoes_Szekeres:
  fixes f :: "_ \<Rightarrow> 'a::linorder"
  shows "(\<exists>S. S \<subseteq> {0..m * n} \<and> card S = m + 1 \<and> gen_mono_on f (\<le>) S) \<or>
         (\<exists>S. S \<subseteq> {0..m * n} \<and> card S = n + 1 \<and> gen_mono_on f (\<ge>) S)"
  by sorry

end
