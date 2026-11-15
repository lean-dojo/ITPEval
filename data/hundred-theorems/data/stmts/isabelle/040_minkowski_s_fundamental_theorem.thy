(*
  File:    Minkowskis_Theorem.thy
  Author:  Manuel Eberl <manuel@pruvisto.org>

  A proof of Blichfeldt's and Minkowski's theorem about the relation between
  subsets of the Euclidean space, the Lebesgue measure, and the integer lattice.
*)
section \<open>Minkowski's theorem\<close>
theory Minkowskis_Theorem
  imports "HOL-Analysis.Equivalence_Lebesgue_Henstock_Integration"
begin

(* Could be generalised to arbitrary euclidean spaces and full-dimensional lattices *)

subsection \<open>Miscellaneous material\<close>

lemma bij_betw_UN:
  assumes "bij_betw f A B"
  shows   "(\<Union>n\<in>A. g (f n)) = (\<Union>n\<in>B. g n)"
  by sorry

definition of_int_vec where
  "of_int_vec v = (\<chi> i. of_int (v $ i))"

lemma of_int_vec_nth [simp]: "of_int_vec v $ n = of_int (v $ n)"
  by sorry

lemma of_int_vec_eq_iff [simp]:
  "(of_int_vec a :: ('a :: ring_char_0) ^ 'n) = of_int_vec b \<longleftrightarrow> a = b"
  by sorry

lemma inj_axis:
  assumes "c \<noteq> 0"
  shows   "inj (\<lambda>k. axis k c :: ('a :: {zero}) ^ 'n)"
  by sorry

lemma compactD:
  assumes "compact (A :: 'a :: metric_space set)" "range f \<subseteq> A"
  shows   "\<exists>h l. strict_mono (h::nat\<Rightarrow>nat) \<and> (f \<circ> h) \<longlonglongrightarrow> l"
  by sorry

lemma closed_lattice:
  fixes A :: "(real ^ 'n) set"
  assumes "\<And>v i. v \<in> A \<Longrightarrow> v $ i \<in> \<int>"
  shows   "closed A"
  by sorry


subsection \<open>Auxiliary theorems about measure theory\<close>

lemma emeasure_lborel_cbox_eq':
  "emeasure lborel (cbox a b) = ennreal (\<Prod>e\<in>Basis. max 0 ((b - a) \<bullet> e))"
  by sorry

lemma emeasure_lborel_cbox_cart_eq:
  fixes a b :: "real ^ ('n :: finite)"
  shows "emeasure lborel (cbox a b) = ennreal (\<Prod>i \<in> UNIV. max 0 ((b - a) $ i))"
  by sorry

lemma sum_emeasure':
  assumes [simp]: "finite A"
  assumes [measurable]: "\<And>x. x \<in> A \<Longrightarrow> B x \<in> sets M"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> emeasure M (B x \<inter> B y) = 0"
  shows   "(\<Sum>x\<in>A. emeasure M (B x)) = emeasure M (\<Union>x\<in>A. B x)"
  by sorry

lemma sums_emeasure':
  assumes [measurable]: "\<And>x. B x \<in> sets M"
  assumes "\<And>x y. x \<noteq> y \<Longrightarrow> emeasure M (B x \<inter> B y) = 0"
  shows   "(\<lambda>x. emeasure M (B x)) sums emeasure M (\<Union>x. B x)"
  by sorry


subsection \<open>Blichfeldt's theorem\<close>

text \<open>
  Blichfeldt's theorem states that, given a subset of $\mathbb{R}^n$ with $n > 0$ and a
  volume of more than 1, there exist two different points in that set whose difference
  vector has integer components.

  This will be the key ingredient in proving Minkowski's theorem.

  Note that in the HOL Light version, it is additionally required -- both for
  Blichfeldt's theorem and for Minkowski's theorem -- that the set is bounded,
  which we do not need.
\<close>
proposition blichfeldt:
  fixes S :: "(real ^ 'n) set"
  assumes [measurable]: "S \<in> sets lebesgue"
  assumes "emeasure lebesgue S > 1"
  obtains x y where "x \<noteq> y" and "x \<in> S" and "y \<in> S" and "\<And>i. (x - y) $ i \<in> \<int>"
  by sorry


subsection \<open>Minkowski's theorem\<close>

text \<open>
  Minkowski's theorem now states that, given a convex subset of $\mathbb{R}^n$ that is
  symmetric around the origin and has a volume greater than $2^n$, that set must contain
  a non-zero point with integer coordinates.
\<close>
theorem minkowski:
  fixes B :: "(real ^ 'n) set"
  assumes "convex B" and symmetric: "uminus ` B \<subseteq> B"
  assumes meas_B [measurable]: "B \<in> sets lebesgue"
  assumes measure_B: "emeasure lebesgue B > 2 ^ CARD('n)"
  obtains x where "x \<in> B" and "x \<noteq> 0" and "\<And>i. x $ i \<in> \<int>"
  by sorry

text \<open>
  If the set in question is compact, the restriction to the volume can be weakened
  to ``at least 1'' from ``greater than 1''.
\<close>
theorem minkowski_compact:
  fixes B :: "(real ^ 'n) set"
  assumes "convex B" and "compact B" and symmetric: "uminus ` B \<subseteq> B"
  assumes measure_B: "emeasure lebesgue B \<ge> 2 ^ CARD('n)"
  obtains x where "x \<in> B" and "x \<noteq> 0" and "\<And>i. x $ i \<in> \<int>"
  by sorry

end
