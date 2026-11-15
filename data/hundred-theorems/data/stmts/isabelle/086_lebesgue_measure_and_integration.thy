(*  Title:      HOL/Analysis/Set_Integral.thy
    Author:     Jeremy Avigad (CMU), Johannes Hölzl (TUM), Luke Serafin (CMU)
    Author:     Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    Author:     Ata Keskin, TU Muenchen

Notation and useful facts for working with integrals over a set.

TODO: keep all these? Need unicode translations as well.
*)

chapter \<open>Integrals over a Set\<close>

theory Set_Integral
  imports Radon_Nikodym
begin

section \<open>Notation\<close>

definition\<^marker>\<open>tag important\<close> "set_borel_measurable M A f \<equiv> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M"

definition\<^marker>\<open>tag important\<close>  "set_integrable M A f \<equiv> integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"

definition\<^marker>\<open>tag important\<close>  "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. indicator A x *\<^sub>R f x)"

syntax
  "_ascii_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  (\<open>(\<open>indent=4 notation=\<open>binder LINT\<close>\<close>LINT (_):(_)/|(_)./ _)\<close> [0,0,0,10] 10)
syntax_consts
  "_ascii_set_lebesgue_integral" == set_lebesgue_integral
translations
  "LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"


section \<open>Basic properties\<close>

lemma set_integrable_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "set_integrable M \<Omega> f = integrable (restrict_space M \<Omega>) f"
  by sorry

lemma set_integrable_cong:
  assumes "M = M'" "A = A'" "\<And>x. x \<in> A \<Longrightarrow> f x = f' x"
  shows   "set_integrable M A f = set_integrable M' A' f'"
  by sorry

lemma set_borel_measurable_sets:
  fixes f :: "_ \<Rightarrow> _::real_normed_vector"
  assumes "set_borel_measurable M X f" "B \<in> sets borel" "X \<in> sets M"
  shows "f -` B \<inter> X \<in> sets M"
  by sorry

lemma set_integrable_bound:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and g :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_borel_measurable M A g"
  assumes "AE x in M. x \<in> A \<longrightarrow> norm (g x) \<le> norm (f x)"
  shows   "set_integrable M A g"
  by sorry

lemma set_lebesgue_integral_zero [simp]: "set_lebesgue_integral M A (\<lambda>x. 0) = 0"
  by sorry

lemma set_lebesgue_integral_cong:
  assumes "A \<in> sets M" and "\<forall>x. x \<in> A \<longrightarrow> f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
  by sorry

lemma set_lebesgue_integral_cong_AE:
  assumes [measurable]: "A \<in> sets M" "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "AE x \<in> A in M. f x = g x"
  shows "(LINT x:A|M. f x) = (LINT x:A|M. g x)"
  by sorry

lemma set_integrable_cong_AE:
    "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    AE x \<in> A in M. f x = g x \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A f = set_integrable M A g"
  by sorry

lemma set_integrable_subset:
  fixes M A B and f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"
  shows "set_integrable M B f"
  by sorry

lemma set_integrable_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f: "set_integrable M S f" and T: "T \<in> sets (restrict_space M S)"
  shows "set_integrable M T f"
  by sorry

(* TODO: integral_cmul_indicator should be named set_integral_const *)
(* TODO: borel_integrable_atLeastAtMost should be named something like set_integrable_Icc_isCont *)

lemma set_integral_scaleR_left: 
  assumes "A \<in> sets M" "c \<noteq> 0 \<Longrightarrow> integrable M f"
  shows "(LINT t:A|M. f t *\<^sub>R c) = (LINT t:A|M. f t) *\<^sub>R c"
  by sorry

lemma set_integral_scaleR_right [simp]: "(LINT t:A|M. a *\<^sub>R f t) = a *\<^sub>R (LINT t:A|M. f t)"
  by sorry

lemma set_integral_mult_right [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(LINT t:A|M. a * f t) = a * (LINT t:A|M. f t)"
  by sorry

lemma set_integral_mult_left [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(LINT t:A|M. f t * a) = (LINT t:A|M. f t) * a"
  by sorry

lemma set_integral_divide_zero [simp]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  shows "(LINT t:A|M. f t / a) = (LINT t:A|M. f t) / a"
  by sorry

lemma set_integrable_scaleR_right [simp, intro]:
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a *\<^sub>R f t)"
  by sorry

lemma set_integrable_scaleR_left [simp, intro]:
  fixes a :: "_ :: {banach, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t *\<^sub>R a)"
  by sorry

lemma set_integrable_mult_right [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. a * f t)"
  by sorry

lemma set_integrable_mult_right_iff [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  assumes "a \<noteq> 0"
  shows "set_integrable M A (\<lambda>t. a * f t) \<longleftrightarrow> set_integrable M A f"
  by sorry

lemma set_integrable_mult_left [simp, intro]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  shows "(a \<noteq> 0 \<Longrightarrow> set_integrable M A f) \<Longrightarrow> set_integrable M A (\<lambda>t. f t * a)"
  by sorry

lemma set_integrable_mult_left_iff [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  assumes "a \<noteq> 0"
  shows "set_integrable M A (\<lambda>t. f t * a) \<longleftrightarrow> set_integrable M A f"
  by sorry

lemma set_integrable_divide [simp, intro]:
  fixes a :: "'a::{real_normed_field, field, second_countable_topology}"
  assumes "a \<noteq> 0 \<Longrightarrow> set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. f t / a)"
  by sorry

lemma set_integrable_mult_divide_iff [simp]:
  fixes a :: "'a::{real_normed_field, second_countable_topology}"
  assumes "a \<noteq> 0"
  shows "set_integrable M A (\<lambda>t. f t / a) \<longleftrightarrow> set_integrable M A f"
  by sorry

lemma set_integral_add [simp, intro]:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x + g x)"
    and "(LINT x:A|M. f x + g x) = (LINT x:A|M. f x) + (LINT x:A|M. g x)"
  by sorry

lemma set_integral_diff [simp, intro]:
  assumes "set_integrable M A f" "set_integrable M A g"
  shows "set_integrable M A (\<lambda>x. f x - g x)" and "(LINT x:A|M. f x - g x) = (LINT x:A|M. f x) - (LINT x:A|M. g x)"
  by sorry

lemma set_integral_uminus: "set_integrable M A f \<Longrightarrow> (LINT x:A|M. - f x) = - (LINT x:A|M. f x)"
  by sorry

lemma set_integral_complex_of_real:
  "(LINT x:A|M. complex_of_real (f x)) = of_real (LINT x:A|M. f x)"
  by sorry

lemma set_integral_mono:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  by sorry

lemma set_integral_mono_AE:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "set_integrable M A f" "set_integrable M A g"
    "AE x \<in> A in M. f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  by sorry

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar> :: real)"
  by sorry

lemma set_integrable_abs_iff:
  fixes f :: "_ \<Rightarrow> real"
  shows "set_borel_measurable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
  by sorry

lemma set_integrable_abs_iff':
  fixes f :: "_ \<Rightarrow> real"
  shows "f \<in> borel_measurable M \<Longrightarrow> A \<in> sets M \<Longrightarrow>
    set_integrable M A (\<lambda>x. \<bar>f x\<bar>) = set_integrable M A f"
  by sorry

lemma set_integrable_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_integrable M A f \<longleftrightarrow> set_integrable M B f"
  by sorry

lemma set_integral_discrete_difference:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable X"
  assumes diff: "(A - B) \<union> (B - A) \<subseteq> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> emeasure M {x} = 0" "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M"
  shows "set_lebesgue_integral M A f = set_lebesgue_integral M B f"
  by sorry

lemma set_integrable_Un:
  fixes f g :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes f_A: "set_integrable M A f" and f_B:  "set_integrable M B f"
    and [measurable]: "A \<in> sets M" "B \<in> sets M"
  shows "set_integrable M (A \<union> B) f"
  by sorry

lemma set_integrable_empty [simp]: "set_integrable M {} f"
  by sorry

lemma set_integrable_UN:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
    "\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets M"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
  by sorry

lemma set_integral_Un:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
shows "(LINT x:A\<union>B|M. f x) = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  by sorry

lemma set_integral_cong_set:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "set_borel_measurable M A f" "set_borel_measurable M B f"
    and ae: "AE x in M. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "(LINT x:B|M. f x) = (LINT x:A|M. f x)"
  by sorry

proposition set_borel_measurable_subset:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "set_borel_measurable M A f" "B \<in> sets M" and "B \<subseteq> A"
  shows "set_borel_measurable M B f"
  by sorry

lemma set_integral_Un_AE:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes ae: "AE x in M. \<not> (x \<in> A \<and> x \<in> B)" and [measurable]: "A \<in> sets M" "B \<in> sets M"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "(LINT x:A\<union>B|M. f x) = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  by sorry

lemma set_integral_finite_Union:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets M"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  by sorry

(* TODO: find a better name? *)
lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) \<longlonglongrightarrow> l"
shows "set_integrable M (\<Union>i. A i) f"
  by sorry

text \<open>Proof from Royden, \emph{Real Analysis}, p. 91.\<close>
lemma lebesgue_integral_countable_add:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
    and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
    and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(LINT x:(\<Union>i. A i)|M. f x) = (\<Sum>i. (LINT x:(A i)|M. f x))"
  by sorry

lemma set_integral_cont_up:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
shows "(\<lambda>i. LINT x:(A i)|M. f x) \<longlonglongrightarrow> (LINT x:(\<Union>i. A i)|M. f x)"
  by sorry

(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  fixes f :: "_ \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes [measurable]: "\<And>i. A i \<in> sets M" and A: "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) \<longlonglongrightarrow> (LINT x:(\<Inter>i. A i)|M. f x)"
  by sorry

lemma set_integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and [simp]: "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * measure M {a}"
  by sorry


section \<open>Complex integrals\<close>

abbreviation complex_integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_integrable M f \<equiv> integrable M f"

abbreviation complex_lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" (\<open>integral\<^sup>C\<close>) where
  "integral\<^sup>C M f == integral\<^sup>L M f"

syntax
  "_complex_lebesgue_integral" :: "pttrn \<Rightarrow> complex \<Rightarrow> 'a measure \<Rightarrow> complex"
 (\<open>(\<open>open_block notation=\<open>binder integral\<close>\<close>\<integral>\<^sup>C _. _ \<partial>_)\<close> [0,0] 110)
syntax_consts
  "_complex_lebesgue_integral" == complex_lebesgue_integral
translations
  "\<integral>\<^sup>Cx. f \<partial>M" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

syntax
  "_ascii_complex_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  (\<open>(\<open>indent=3 notation=\<open>binder CLINT\<close>\<close>CLINT _|_. _)\<close> [0,0,10] 10)
syntax_consts
  "_ascii_complex_lebesgue_integral" == complex_lebesgue_integral
translations
  "CLINT x|M. f" == "CONST complex_lebesgue_integral M (\<lambda>x. f)"

lemma complex_integrable_cnj [simp]:
  "complex_integrable M (\<lambda>x. cnj (f x)) \<longleftrightarrow> complex_integrable M f"
  by sorry

lemma complex_of_real_integrable_eq:
  "complex_integrable M (\<lambda>x. complex_of_real (f x)) \<longleftrightarrow> integrable M f"
  by sorry


abbreviation complex_set_integrable :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> bool" where
  "complex_set_integrable M A f \<equiv> set_integrable M A f"

abbreviation complex_set_lebesgue_integral :: "'a measure \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where
  "complex_set_lebesgue_integral M A f \<equiv> set_lebesgue_integral M A f"

syntax
  "_ascii_complex_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
  (\<open>(\<open>indent=4 notation=\<open>binder CLINT\<close>\<close>CLINT _:_|_. _)\<close> [0,0,0,10] 10)
syntax_consts
  "_ascii_complex_set_lebesgue_integral" == complex_set_lebesgue_integral
translations
  "CLINT x:A|M. f" == "CONST complex_set_lebesgue_integral M A (\<lambda>x. f)"

lemma set_measurable_continuous_on:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "A \<in> sets borel \<Longrightarrow> continuous_on A f \<Longrightarrow> set_borel_measurable borel A f"
  by sorry

section \<open>NN Set Integrals\<close>

text\<open>This notation is from Sébastien Gouëzel: His use is not directly in line with the
notations in this file, they are more in line with sum, and more readable he thinks.\<close>

abbreviation "set_nn_integral M A f \<equiv> nn_integral M (\<lambda>x. f x * indicator A x)"

syntax
  "_set_nn_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
    (\<open>(\<open>notation=\<open>binder integral\<close>\<close>\<integral>\<^sup>+((_)\<in>(_)./ _)/\<partial>_)\<close> [0,0,0,110] 10)
  "_set_lebesgue_integral" :: "pttrn => 'a set => 'a measure => ereal => ereal"
    (\<open>(\<open>notation=\<open>binder integral\<close>\<close>\<integral>((_)\<in>(_)./ _)/\<partial>_)\<close> [0,0,0,110] 10)
syntax_consts
  "_set_nn_integral" == set_nn_integral and
  "_set_lebesgue_integral" == set_lebesgue_integral
translations
  "\<integral>\<^sup>+x \<in> A. f \<partial>M" == "CONST set_nn_integral M A (\<lambda>x. f)"
  "\<integral>x \<in> A. f \<partial>M" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

lemma set_nn_integral_cong:
  assumes "M = M'" "A = B" "\<And>x. x \<in> space M \<inter> A \<Longrightarrow> f x = g x"
  shows   "set_nn_integral M A f = set_nn_integral M' B g"
  by sorry

lemma nn_integral_disjoint_pair:
  assumes [measurable]: "f \<in> borel_measurable M"
          "B \<in> sets M" "C \<in> sets M"
          "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M) + (\<integral>\<^sup>+x \<in> C. f x \<partial>M)"
  by sorry

lemma nn_integral_disjoint_pair_countspace:
  assumes "B \<inter> C = {}"
  shows "(\<integral>\<^sup>+x \<in> B \<union> C. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+x \<in> B. f x \<partial>count_space UNIV) + (\<integral>\<^sup>+x \<in> C. f x \<partial>count_space UNIV)"
  by sorry

lemma nn_integral_null_delta:
  assumes "A \<in> sets M" "B \<in> sets M"
          "(A - B) \<union> (B - A) \<in> null_sets M"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> B. f x \<partial>M)"
  by sorry

proposition nn_integral_disjoint_family:
  assumes [measurable]: "f \<in> borel_measurable M" "\<And>(n::nat). B n \<in> sets M"
      and "disjoint_family B"
  shows "(\<integral>\<^sup>+x \<in> (\<Union>n. B n). f x \<partial>M) = (\<Sum>n. (\<integral>\<^sup>+x \<in> B n. f x \<partial>M))"
  by sorry

lemma nn_set_integral_add:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
  shows "(\<integral>\<^sup>+x \<in> A. (f x + g x) \<partial>M) = (\<integral>\<^sup>+x \<in> A. f x \<partial>M) + (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
  by sorry

lemma nn_set_integral_cong:
  assumes "AE x in M. f x = g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
  by sorry

lemma nn_set_integral_set_mono:
  "A \<subseteq> B \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+ x \<in> B. f x \<partial>M)"
  by sorry

lemma nn_set_integral_mono:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
          "A \<in> sets M"
      and "AE x\<in>A in M. f x \<le> g x"
  shows "(\<integral>\<^sup>+x \<in> A. f x \<partial>M) \<le> (\<integral>\<^sup>+x \<in> A. g x \<partial>M)"
  by sorry

lemma nn_set_integral_space [simp]:
  shows "(\<integral>\<^sup>+ x \<in> space M. f x \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
  by sorry

lemma nn_integral_count_compose_inj:
  assumes "inj_on g A"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> g`A. f y \<partial>count_space UNIV)"
  by sorry

lemma nn_integral_count_compose_bij:
  assumes "bij_betw g A B"
  shows "(\<integral>\<^sup>+x \<in> A. f (g x) \<partial>count_space UNIV) = (\<integral>\<^sup>+y \<in> B. f y \<partial>count_space UNIV)"
  by sorry

lemma set_integral_null_delta:
  fixes f::"_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes [measurable]: "integrable M f" "A \<in> sets M" "B \<in> sets M"
    and null: "(A - B) \<union> (B - A) \<in> null_sets M"
  shows "(\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> B. f x \<partial>M)"
  by sorry

lemma set_integral_space:
  assumes "integrable M f"
  shows "(\<integral>x \<in> space M. f x \<partial>M) = (\<integral>x. f x \<partial>M)"
  by sorry

lemma null_if_pos_func_has_zero_nn_int:
  fixes f::"'a \<Rightarrow> ennreal"
  assumes [measurable]: "f \<in> borel_measurable M" "A \<in> sets M"
    and "AE x\<in>A in M. f x > 0" "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = 0"
  shows "A \<in> null_sets M"
  by sorry

lemma null_if_pos_func_has_zero_int:
  assumes [measurable]: "integrable M f" "A \<in> sets M"
      and "AE x\<in>A in M. f x > 0" "(\<integral>x\<in>A. f x \<partial>M) = (0::real)"
  shows "A \<in> null_sets M"
  by sorry
                                    
text\<open>The next lemma is a variant of \<open>density_unique\<close>. Note that it uses the notation
for nonnegative set integrals introduced earlier.\<close>

lemma (in sigma_finite_measure) density_unique2:
  assumes [measurable]: "f \<in> borel_measurable M" "f' \<in> borel_measurable M"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x \<in> A. f x \<partial>M) = (\<integral>\<^sup>+ x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
  by sorry


text \<open>The next lemma implies the same statement for Banach-space valued functions
using Hahn-Banach theorem and linear forms. Since they are not yet easily available, I
only formulate it for real-valued functions.\<close>

lemma density_unique_real:
  fixes f f'::"_ \<Rightarrow> real"
  assumes M[measurable]: "integrable M f" "integrable M f'"
  assumes density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>x \<in> A. f x \<partial>M) = (\<integral>x \<in> A. f' x \<partial>M)"
  shows "AE x in M. f x = f' x"
  by sorry

section \<open>Scheffé's lemma\<close>

text \<open>The next lemma shows that \<open>L\<^sup>1\<close> convergence of a sequence of functions follows from almost
everywhere convergence and the weaker condition of the convergence of the integrated norms (or even
just the nontrivial inequality about them). Useful in a lot of contexts! This statement (or its
variations) are known as Scheffe lemma.

The formalization is more painful as one should jump back and forth between reals and ereals and justify
all the time positivity or integrability (thankfully, measurability is handled more or less automatically).\<close>

proposition Scheffe_lemma1:
  assumes "\<And>n. integrable M (F n)" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "limsup (\<lambda>n. \<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
  by sorry

proposition Scheffe_lemma2:
  fixes F::"nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<And> n::nat. F n \<in> borel_measurable M" "integrable M f"
          "AE x in M. (\<lambda>n. F n x) \<longlonglongrightarrow> f x"
          "\<And>n. (\<integral>\<^sup>+ x. norm(F n x) \<partial>M) \<le> (\<integral>\<^sup>+ x. norm(f x) \<partial>M)"
  shows "(\<lambda>n. \<integral>\<^sup>+ x. norm(F n x - f x) \<partial>M) \<longlonglongrightarrow> 0"
  by sorry

lemma tendsto_set_lebesgue_integral_at_right:
  fixes a b :: real and f :: "real \<Rightarrow> 'a :: {banach,second_countable_topology}"
  assumes "a < b" and sets: "\<And>a'. a' \<in> {a<..b} \<Longrightarrow> {a'..b} \<in> sets M"
      and "set_integrable M {a<..b} f"
  shows   "((\<lambda>a'. set_lebesgue_integral M {a'..b} f) \<longlongrightarrow>
             set_lebesgue_integral M {a<..b} f) (at_right a)"
  by sorry

section \<open>Convergence of integrals over an interval\<close>

text \<open>
  The next lemmas relate convergence of integrals over an interval to
  improper integrals.
\<close>
lemma tendsto_set_lebesgue_integral_at_left:
  fixes a b :: real and f :: "real \<Rightarrow> 'a :: {banach,second_countable_topology}"
  assumes "a < b" and sets: "\<And>b'. b' \<in> {a..<b} \<Longrightarrow> {a..b'} \<in> sets M"
      and "set_integrable M {a..<b} f"
  shows   "((\<lambda>b'. set_lebesgue_integral M {a..b'} f) \<longlongrightarrow>
             set_lebesgue_integral M {a..<b} f) (at_left b)"
  by sorry

proposition tendsto_set_lebesgue_integral_at_top:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes sets: "\<And>b. b \<ge> a \<Longrightarrow> {a..b} \<in> sets M"
      and int: "set_integrable M {a..} f"
  shows "((\<lambda>b. set_lebesgue_integral M {a..b} f) \<longlongrightarrow> set_lebesgue_integral M {a..} f) at_top"
  by sorry

proposition tendsto_set_lebesgue_integral_at_bot:
  fixes f :: "real \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes sets: "\<And>a. a \<le> b \<Longrightarrow> {a..b} \<in> sets M"
      and int: "set_integrable M {..b} f"
    shows "((\<lambda>a. set_lebesgue_integral M {a..b} f) \<longlongrightarrow> set_lebesgue_integral M {..b} f) at_bot"
  by sorry



theorem integral_Markov_inequality':
  fixes u :: "'a \<Rightarrow> real"
  assumes [measurable]: "set_integrable M A u" and "A \<in> sets M"
  assumes "AE x in M. x \<in> A \<longrightarrow> u x \<ge> 0" and "0 < (c::real)"
  shows "emeasure M {x\<in>A. u x \<ge> c} \<le> (1/c::real) * (\<integral>x\<in>A. u x \<partial>M)"
  by sorry

theorem integral_Markov_inequality'_measure:
  assumes [measurable]: "set_integrable M A u" and "A \<in> sets M" 
     and "AE x in M. x \<in> A \<longrightarrow> 0 \<le> u x" "0 < (c::real)"
  shows "measure M {x\<in>A. u x \<ge> c} \<le> (\<integral>x\<in>A. u x \<partial>M) / c"
  by sorry

theorem%important (in finite_measure) Chernoff_ineq_ge:
  assumes s: "s > 0"
  assumes integrable: "set_integrable M A (\<lambda>x. exp (s * f x))" and "A \<in> sets M"
  shows   "measure M {x\<in>A. f x \<ge> a} \<le> exp (-s * a) * (\<integral>x\<in>A. exp (s * f x) \<partial>M)"
  by sorry

theorem%important (in finite_measure) Chernoff_ineq_le:
  assumes s: "s > 0"
  assumes integrable: "set_integrable M A (\<lambda>x. exp (-s * f x))" and "A \<in> sets M"
  shows   "measure M {x\<in>A. f x \<le> a} \<le> exp (s * a) * (\<integral>x\<in>A. exp (-s * f x) \<partial>M)"
  by sorry


section \<open>Integrable Simple Functions\<close>

text \<open>This section is from the Martingales AFP entry, by Ata Keskin, TU München\<close>

text \<open>We restate some basic results concerning Bochner-integrable functions.\<close>
  
lemma integrable_implies_simple_function_sequence:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable M f"
  obtains s where "\<And>i. simple_function M (s i)"
      and "\<And>i. emeasure M {y \<in> space M. s i y \<noteq> 0} \<noteq> \<infinity>"
      and "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. s i x) \<longlonglongrightarrow> f x"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> 2 * norm (f x)"
  by sorry

text \<open>Simple functions can be represented by sums of indicator functions.\<close>

lemma simple_function_indicator_representation_banach:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "simple_function M f" "x \<in> space M"
  shows "f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"
  (is "?l = ?r")
  by sorry

lemma simple_function_indicator_representation_AE:
  fixes f ::"'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "simple_function M f"
  shows "AE x in M. f x = (\<Sum>y \<in> f ` space M. indicator (f -` {y} \<inter> space M) x *\<^sub>R y)"  
  by sorry

lemmas simple_function_scaleR[intro] = simple_function_compose2[where h="(*\<^sub>R)"]
lemmas integrable_simple_function = simple_bochner_integrable.intros[THEN has_bochner_integral_simple_bochner_integrable, THEN integrable.intros] 

text \<open>Induction rule for simple integrable functions.\<close>

lemma\<^marker>\<open>tag important\<close> integrable_simple_function_induct[consumes 2, case_names cong indicator add, induct set: simple_function]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> 
                    \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> 
                    \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes indicator: "\<And>A y. A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>z. z \<in> space M \<Longrightarrow> norm (f z + g z) = norm (f z) + norm (g z)) \<Longrightarrow>
                      P f \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  shows "P f"
  by sorry

text \<open>Induction rule for non-negative simple integrable functions\<close>
lemma\<^marker>\<open>tag important\<close> integrable_simple_function_induct_nn[consumes 3, case_names cong indicator add, induct set: simple_function]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes f: "simple_function M f" "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" "\<And>x. x \<in> space M \<longrightarrow> f x \<ge> 0"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes indicator: "\<And>A y. y \<ge> 0 \<Longrightarrow> A \<in> sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> P (\<lambda>x. indicator A x *\<^sub>R y)"
  assumes add: "\<And>f g. (\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> simple_function M f \<Longrightarrow> emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0) \<Longrightarrow> simple_function M g \<Longrightarrow> emeasure M {y \<in> space M. g y \<noteq> 0} \<noteq> \<infinity> \<Longrightarrow> 
                      (\<And>z. z \<in> space M \<Longrightarrow> norm (f z + g z) = norm (f z) + norm (g z)) \<Longrightarrow>
                      P f \<Longrightarrow> P g \<Longrightarrow> P (\<lambda>x. f x + g x)"
  shows "P f"
  by sorry

lemma finite_nn_integral_imp_ae_finite:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>"
  shows "AE x in M. f x < \<infinity>"
  by sorry

text \<open>Convergence in L1-Norm implies existence of a subsequence which convergences almost everywhere. 
      This lemma is easier to use than the existing one in \<^theory>\<open>HOL-Analysis.Bochner_Integration\<close>\<close>

lemma cauchy_L1_AE_cauchy_subseq:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes [measurable]: "\<And>n. integrable M (s n)"
      and "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. LINT x|M. norm (s i x - s j x) < e"
  obtains r where "strict_mono r" "AE x in M. Cauchy (\<lambda>i. s (r i) x)"
  by sorry

subsection \<open>Totally Ordered Banach Spaces\<close>

lemma integrable_max[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology}"
  assumes fg[measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. max (f x) (g x))"
  by sorry

lemma integrable_min[simp, intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology}"
  assumes [measurable]: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>x. min (f x) (g x))"
  by sorry

text \<open>Restatement of \<open>integral_nonneg_AE\<close> for functions taking values in a Banach space.\<close>
lemma integral_nonneg_AE_banach:                        
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes [measurable]: "f \<in> borel_measurable M" and nonneg: "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^sup>L M f"
  by sorry

lemma integral_mono_AE_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "AE x in M. f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  by sorry

lemma integral_mono_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  by sorry

subsection \<open>Auxiliary Lemmas for Set Integrals\<close>

lemma nn_set_integral_eq_set_integral:
  assumes [measurable]:"integrable M f"
      and "AE x \<in> A in M. 0 \<le> f x" "A \<in> sets M"
    shows "(\<integral>\<^sup>+x\<in>A. f x \<partial>M) = (\<integral> x \<in> A. f x \<partial>M)"
  by sorry

lemma set_integral_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "set_lebesgue_integral (restrict_space M \<Omega>) A f = set_lebesgue_integral M A (\<lambda>x. indicator \<Omega> x *\<^sub>R f x)"
  by sorry

lemma set_integral_const:
  fixes c :: "'b::{banach, second_countable_topology}"
  assumes "A \<in> sets M" "emeasure M A \<noteq> \<infinity>"
  shows "set_lebesgue_integral M A (\<lambda>_. c) = measure M A *\<^sub>R c"
  by sorry

lemma set_integral_mono_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "set_integrable M A f" "set_integrable M A g"
    "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "(LINT x:A|M. f x) \<le> (LINT x:A|M. g x)"
  by sorry

lemma set_integral_mono_AE_banach:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "set_integrable M A f" "set_integrable M A g" "AE x\<in>A in M. f x \<le> g x"
  shows "set_lebesgue_integral M A f \<le> set_lebesgue_integral M A g" using assms unfolding set_lebesgue_integral_def by (auto simp add: set_integrable_def intro!: integral_mono_AE_banach[of M "\<lambda>x. indicator A x *\<^sub>R f x" "\<lambda>x. indicator A x *\<^sub>R g x"], simp add: indicator_def)

subsection \<open>Integrability and Measurability of the Diameter\<close>

context
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}" and M
  assumes bounded: "\<And>x. x \<in> space M \<Longrightarrow> bounded (range (\<lambda>i. s i x))"
begin

lemma borel_measurable_diameter: 
  assumes [measurable]: "\<And>i. (s i) \<in> borel_measurable M"
  shows "(\<lambda>x. diameter {s i x |i. n \<le> i}) \<in> borel_measurable M"
  by sorry

lemma integrable_bound_diameter:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f" 
      and [measurable]: "\<And>i. (s i) \<in> borel_measurable M"
      and "\<And>x i. x \<in> space M \<Longrightarrow> norm (s i x) \<le> f x"
    shows "integrable M (\<lambda>x. diameter {s i x |i. n \<le> i})"
  by sorry
end    

subsection \<open>Averaging Theorem\<close>

text \<open>We aim to lift results from the real case to arbitrary Banach spaces. 
      Our fundamental tool in this regard will be the averaging theorem. The proof of this theorem is due to Serge Lang (Real and Functional Analysis) \<^cite>\<open>"Lang_1993"\<close>. 
      The theorem allows us to make statements about a function's value almost everywhere, depending on the value its integral takes on various sets of the measure space.\<close>

text \<open>Before we introduce and prove the averaging theorem, we will first show the following lemma which is crucial for our proof. 
      While not stated exactly in this manner, our proof makes use of the characterization of second-countable topological spaces given in the book General Topology by Ryszard Engelking (Theorem 4.1.15) \<^cite>\<open>"engelking_1989"\<close>.
    (Engelking's book \emph{General Topology})\<close>

lemma balls_countable_basis:
  obtains D :: "'a :: {metric_space, second_countable_topology} set" 
  where "topological_basis (case_prod ball ` (D \<times> (\<rat> \<inter> {0<..})))"
    and "countable D"
    and "D \<noteq> {}"    
  by sorry

context sigma_finite_measure
begin         

text \<open>To show statements concerning \<open>\<sigma>\<close>-finite measure spaces, one usually shows the statement for finite measure spaces and uses a limiting argument to show it for the \<open>\<sigma>\<close>-finite case.
      The following induction scheme formalizes this.\<close>
lemma sigma_finite_measure_induct[case_names finite_measure, consumes 0]:
  assumes "\<And>(N :: 'a measure) \<Omega>. finite_measure N 
                              \<Longrightarrow> N = restrict_space M \<Omega>
                              \<Longrightarrow> \<Omega> \<in> sets M 
                              \<Longrightarrow> emeasure N \<Omega> \<noteq> \<infinity> 
                              \<Longrightarrow> emeasure N \<Omega> \<noteq> 0 
                              \<Longrightarrow> almost_everywhere N Q"
      and [measurable]: "Measurable.pred M Q"
  shows "almost_everywhere M Q"
  by sorry

text \<open>Real Functional Analysis - Lang\<close>
text \<open>The Averaging Theorem allows us to make statements concerning how a function behaves almost everywhere, depending on its behaviour on average.\<close>
lemma averaging_theorem:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes [measurable]: "integrable M f" 
      and closed: "closed S"
      and "\<And>A. A \<in> sets M \<Longrightarrow> measure M A > 0 \<Longrightarrow> (1 / measure M A) *\<^sub>R set_lebesgue_integral M A f \<in> S"
    shows "AE x in M. f x \<in> S"
  by sorry
  
lemma density_zero:
  fixes f::"'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f"
      and density_0: "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f = 0"
  shows "AE x in M. f x = 0"
  by sorry

text \<open>The following lemma shows that densities are unique in Banach spaces.\<close>
lemma density_unique_banach:
  fixes f f'::"'a \<Rightarrow> 'b::{second_countable_topology, banach}"
  assumes "integrable M f" "integrable M f'"
      and density_eq: "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f = set_lebesgue_integral M A f'"
  shows "AE x in M. f x = f' x"
  by sorry

lemma density_nonneg:
  fixes f::"_ \<Rightarrow> 'b::{second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" 
      and "\<And>A. A \<in> sets M \<Longrightarrow> set_lebesgue_integral M A f \<ge> 0"
    shows "AE x in M. f x \<ge> 0"
  by sorry

corollary integral_nonneg_eq_0_iff_AE_banach:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes f[measurable]: "integrable M f" and nonneg: "AE x in M. 0 \<le> f x"
  shows "integral\<^sup>L M f = 0 \<longleftrightarrow> (AE x in M. f x = 0)"
  by sorry

corollary integral_eq_mono_AE_eq_AE:
  fixes f g :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach, linorder_topology, ordered_real_vector}"
  assumes "integrable M f" "integrable M g" "integral\<^sup>L M f = integral\<^sup>L M g" "AE x in M. f x \<le> g x" 
  shows "AE x in M. f x = g x"
  by sorry

end

end
