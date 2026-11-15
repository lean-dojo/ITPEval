(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Derangements\<close>

theory Derangements
imports
  Complex_Main
  "HOL-Combinatorics.Permutations"
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to @{theory HOL.Finite_Set} Theory\<close>

lemma card_product_dependent:
  assumes "finite S" "\<forall>x \<in> S. finite (T x)"
  shows "card {(x, y). x \<in> S \<and> y \<in> T x} = (\<Sum>x \<in> S. card (T x))"
  by sorry


subsubsection \<open>Additions to @{theory "HOL-Combinatorics.Permutations"} Theory\<close>

lemma permutes_imp_bij':
  assumes "p permutes S"
  shows "bij p"
  by sorry

lemma permutesE:
  assumes "p permutes S"
  obtains "bij p" "\<forall>x. x \<notin> S \<longrightarrow> p x = x"
  by sorry

lemma bij_imp_permutes':
  assumes "bij p" "\<forall>x. x \<notin> A \<longrightarrow> p x = x"
  shows  "p permutes A"
  by sorry

lemma permutes_swap:
  assumes "p permutes S"
  shows "Fun.swap x y p permutes (insert x (insert y S))"
  by sorry

lemma bij_extends:
  "bij p \<Longrightarrow> p x = x \<Longrightarrow> bij (p(x := y, inv p y := x))"
  by sorry

lemma permutes_add_one:
  assumes "p permutes S" "x \<notin> S" "y \<in> S"
  shows "p(x := y, inv p y := x) permutes (insert x S)"
  by sorry

lemma permutations_skip_one:
  assumes "p permutes S" "x : S"
  shows "p(x := x, inv p x := p x) permutes (S - {x})"
  by sorry

lemma permutes_drop_cycle_size_two:
  \<open>p \<circ> Transposition.transpose x (p x) permutes (S - {x, p x})\<close>
  if \<open>p permutes S\<close> \<open>p (p x) = x\<close>
  by sorry


subsection \<open>Fixpoint-Free Permutations\<close>

definition derangements :: "nat set \<Rightarrow> (nat \<Rightarrow> nat) set"
where
  "derangements S = {p. p permutes S \<and> (\<forall>x \<in> S. p x \<noteq> x)}"

lemma derangementsI:
  assumes "p permutes S" "\<And>x. x \<in> S \<Longrightarrow> p x \<noteq> x"
  shows "p \<in> derangements S"
  by sorry

lemma derangementsE:
  assumes "d : derangements S"
  obtains "d permutes S" "\<forall>x\<in>S. d x \<noteq> x"
  by sorry


subsection \<open>Properties of Derangements\<close>

lemma derangements_inv:
  assumes d: "d \<in> derangements S"
  shows "inv d \<in> derangements S"
  by sorry

lemma derangements_in_image:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "d x \<in> A"
  by sorry

lemma derangements_in_image_strong:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "d x \<in> A - {x}"
  by sorry

lemma derangements_inverse_in_image:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "inv d x \<in> A"
  by sorry

lemma derangements_fixpoint:
  assumes "d \<in> derangements A" "x \<notin> A"
  shows "d x = x"
  by sorry

lemma derangements_no_fixpoint:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "d x \<noteq> x"
  by sorry

lemma finite_derangements:
  assumes "finite A"
  shows "finite (derangements A)"
  by sorry

subsection \<open>Construction of Derangements\<close>

lemma derangements_empty[simp]:
  "derangements {} = {id}"
  by sorry

lemma derangements_singleton[simp]:
  "derangements {x} = {}"
  by sorry

lemma derangements_swap:
  assumes "d \<in> derangements S" "x \<notin> S" "y \<notin> S" "x \<noteq> y"
  shows "Fun.swap x y d \<in> derangements (insert x (insert y S))"
  by sorry

lemma derangements_skip_one:
  assumes d: "d \<in> derangements S" and "x \<in> S" "d (d x) \<noteq> x"
  shows "d(x := x, inv d x := d x) \<in> derangements (S - {x})"
  by sorry

lemma derangements_add_one:
  assumes "d \<in> derangements S" "x \<notin> S" "y \<in> S"
  shows "d(x := y, inv d y := x) \<in> derangements (insert x S)"
  by sorry

lemma derangements_drop_minimal_cycle:
  assumes "d \<in> derangements S" "d (d x) = x"
  shows "Fun.swap x (d x) d \<in> derangements (S - {x, d x})"
  by sorry


subsection \<open>Cardinality of Derangements\<close>

subsubsection \<open>Recursive Characterization\<close>

fun count_derangements :: "nat \<Rightarrow> nat"
where
  "count_derangements 0 = 1"
| "count_derangements (Suc 0) = 0"
| "count_derangements (Suc (Suc n)) = (n + 1) * (count_derangements (Suc n) + count_derangements n)"

lemma card_derangements:
  assumes "finite S" "card S = n"
  shows "card (derangements S) = count_derangements n"
  by sorry


subsubsection \<open>Closed-Form Characterization\<close>

lemma count_derangements:
  "real (count_derangements n) = fact n * (\<Sum>k \<in> {0..n}. (-1) ^ k / fact k)"
  by sorry


subsubsection \<open>Approximation of Cardinality\<close>

lemma two_power_fact_le_fact:
  assumes "n \<ge> 1"
  shows   "2^k * fact n \<le> (fact (n + k) :: 'a :: {semiring_char_0,linordered_semidom})"
  by sorry

lemma exp1_approx:
  assumes "n > 0"
  shows   "exp (1::real) - (\<Sum>k<n. 1 / fact k) \<in> {0..2 / fact n}"
  by sorry

lemma exp1_bounds: "exp 1 \<in> {8 / 3..11 / 4 :: real}"
  by sorry

lemma count_derangements_approximation:
  assumes "n \<noteq> 0"
  shows "abs(real (count_derangements n) - fact n / exp 1) < 1 / 2"
  by sorry

theorem derangements_formula:
  assumes "n \<noteq> 0" "finite S" "card S = n"
  shows "int (card (derangements S)) = round (fact n / exp 1 :: real)"
  by sorry

theorem derangements_formula':
  assumes "n \<noteq> 0" "finite S" "card S = n"
  shows "card (derangements S) = nat (round (fact n / exp 1 :: real))"
  by sorry

end
