(*  Title:      HOL/Analysis/Continuum_Not_Denumerable.thy
    Author:     Benjamin Porter, Monash University, NICTA, 2005
    Author:     Johannes Hölzl, TU München
*)

section \<open>Non-Denumerability of the Continuum\<close>

theory Continuum_Not_Denumerable
imports
  Complex_Main 
  "HOL-Library.Countable_Set"
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Abstract\<close>

text \<open>
  The following document presents a proof that the Continuum is uncountable.
  It is formalised in the Isabelle/Isar theorem proving system.

  \<^bold>\<open>Theorem:\<close> The Continuum \<open>\<real>\<close> is not denumerable. In other words, there does
  not exist a function \<open>f: \<nat> \<Rightarrow> \<real>\<close> such that \<open>f\<close> is surjective.

  \<^bold>\<open>Outline:\<close> An elegant informal proof of this result uses Cantor's
  Diagonalisation argument. The proof presented here is not this one.

  First we formalise some properties of closed intervals, then we prove the
  Nested Interval Property. This property relies on the completeness of the
  Real numbers and is the foundation for our argument. Informally it states
  that an intersection of countable closed intervals (where each successive
  interval is a subset of the last) is non-empty. We then assume a surjective
  function \<open>f: \<nat> \<Rightarrow> \<real>\<close> exists and find a real \<open>x\<close> such that \<open>x\<close> is not in the
  range of \<open>f\<close> by generating a sequence of closed intervals then using the
  Nested Interval Property.
\<close>
text\<^marker>\<open>tag important\<close> \<open>%whitespace\<close>
theorem real_non_denum: "\<nexists>f :: nat \<Rightarrow> real. surj f"
  by sorry

lemma uncountable_UNIV_real: "uncountable (UNIV :: real set)"
  by sorry

corollary complex_non_denum: "\<nexists>f :: nat \<Rightarrow> complex. surj f"
  by sorry

lemma uncountable_UNIV_complex: "uncountable (UNIV :: complex set)"
  by sorry

lemma bij_betw_open_intervals:
  fixes a b c d :: real
  assumes "a < b" "c < d"
  shows "\<exists>f. bij_betw f {a<..<b} {c<..<d}"
  by sorry

lemma bij_betw_tan: "bij_betw tan {-pi/2<..<pi/2} UNIV"
  by sorry

lemma uncountable_open_interval: "uncountable {a<..<b} \<longleftrightarrow> a < b" for a b :: real
  by sorry

lemma uncountable_half_open_interval_1: "uncountable {a..<b} \<longleftrightarrow> a < b" for a b :: real
  by sorry

lemma uncountable_half_open_interval_2: "uncountable {a<..b} \<longleftrightarrow> a < b" for a b :: real
  by sorry

lemma real_interval_avoid_countable_set:
  fixes a b :: real and A :: "real set"
  assumes "a < b" and "countable A"
  shows "\<exists>x\<in>{a<..<b}. x \<notin> A"
  by sorry

lemma uncountable_closed_interval: "uncountable {a..b} \<longleftrightarrow> a < b" for a b :: real
  by sorry

lemma open_minus_countable:
  fixes S A :: "real set"
  assumes "countable A" "S \<noteq> {}" "open S"
  shows "\<exists>x\<in>S. x \<notin> A"
  by sorry

end
