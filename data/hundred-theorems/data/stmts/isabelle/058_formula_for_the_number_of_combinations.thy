(*  Title:      HOL/Binomial.thy
    Author:     Jacques D. Fleuriot
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
    Author:     Chaitanya Mangla
    Author:     Manuel Eberl
*)

section \<open>Binomial Coefficients, Binomial Theorem, Inclusion-exclusion Principle\<close>

theory Binomial
  imports Presburger Factorial
begin

subsection \<open>Binomial coefficients\<close>

text \<open>This development is based on the work of Andy Gordon and Florian Kammueller.\<close>

text \<open>Combinatorial definition\<close>

definition binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "binomial n k = card {K\<in>Pow {0..<n}. card K = k}"

open_bundle binomial_syntax
begin
notation binomial  (infix \<open>choose\<close> 64)
end

lemma binomial_right_mono:
  assumes "m \<le> n" shows "m choose k \<le> n choose k"
  by sorry

theorem n_subsets:
  assumes "finite A"
  shows "card {B. B \<subseteq> A \<and> card B = k} = card A choose k"
  by sorry

text \<open>Recursive characterization\<close>

lemma binomial_n_0 [simp]: "n choose 0 = 1"
  by sorry

lemma binomial_0_Suc [simp]: "0 choose Suc k = 0"
  by sorry

lemma binomial_Suc_Suc [simp]: "Suc n choose Suc k = (n choose k) + (n choose Suc k)"
  by sorry

lemma binomial_eq_0: "n < k \<Longrightarrow> n choose k = 0"
  by sorry

lemma zero_less_binomial: "k \<le> n \<Longrightarrow> n choose k > 0"
  by sorry

lemma binomial_eq_0_iff [simp]: "n choose k = 0 \<longleftrightarrow> n < k"
  by sorry

lemma zero_less_binomial_iff [simp]: "n choose k > 0 \<longleftrightarrow> k \<le> n"
  by sorry

lemma binomial_n_n [simp]: "n choose n = 1"
  by sorry

lemma binomial_Suc_n [simp]: "Suc n choose n = Suc n"
  by sorry

lemma binomial_1 [simp]: "n choose Suc 0 = n"
  by sorry

lemma choose_one: "n choose 1 = n" for n :: nat
  by sorry

lemma choose_reduce_nat:
  "0 < n \<Longrightarrow> 0 < k \<Longrightarrow>
    n choose k = ((n - 1) choose (k - 1)) + ((n - 1) choose k)"
  by sorry

lemma Suc_times_binomial_eq: "Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
  by sorry

lemma binomial_le_pow2: "n choose k \<le> 2^n"
  by sorry

text \<open>The absorption property.\<close>
lemma Suc_times_binomial: "Suc k * (Suc n choose Suc k) = Suc n * (n choose k)"
  by sorry

text \<open>This is the well-known version of absorption, but it's harder to use
  because of the need to reason about division.\<close>
lemma binomial_Suc_Suc_eq_times: "(Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
  by sorry

text \<open>Another version of absorption, with \<open>-1\<close> instead of \<open>Suc\<close>.\<close>
lemma times_binomial_minus1_eq: "0 < k \<Longrightarrow> k * (n choose k) = n * ((n - 1) choose (k - 1))"
  by sorry


subsection \<open>The binomial theorem (courtesy of Tobias Nipkow):\<close>

text \<open>Avigad's version, generalized to any commutative ring\<close>
theorem (in comm_semiring_1) binomial_ring:
  "(a + b :: 'a)^n = (\<Sum>k\<le>n. (of_nat (n choose k)) * a^k * b^(n-k))"
  by sorry


text \<open>Original version for the naturals.\<close>
corollary binomial: "(a + b :: nat)^n = (\<Sum>k\<le>n. (of_nat (n choose k)) * a^k * b^(n - k))"
  by sorry

lemma binomial_fact_lemma: "k \<le> n \<Longrightarrow> fact k * fact (n - k) * (n choose k) = fact n"
  by sorry

lemma binomial_fact':
  assumes "k \<le> n"
  shows "n choose k = fact n div (fact k * fact (n - k))"
  by sorry

lemma binomial_fact:
  assumes kn: "k \<le> n"
  shows "(of_nat (n choose k) :: 'a::field_char_0) = fact n / (fact k * fact (n - k))"
  by sorry

lemma fact_binomial:
  assumes "k \<le> n"
  shows "fact k * of_nat (n choose k) = (fact n / fact (n - k) :: 'a::field_char_0)"
  by sorry

lemma binomial_fact_pow: "(n choose s) * fact s \<le> n^s"
  by sorry

lemma choose_two: "n choose 2 = n * (n - 1) div 2"
  by sorry

lemma choose_row_sum: "(\<Sum>k\<le>n. n choose k) = 2^n"
  by sorry

lemma sum_choose_lower: "(\<Sum>k\<le>n. (r+k) choose k) = Suc (r+n) choose n"
  by sorry

lemma sum_choose_upper: "(\<Sum>k\<le>n. k choose m) = Suc n choose Suc m"
  by sorry

lemma choose_alternating_sum:
  "n > 0 \<Longrightarrow> (\<Sum>i\<le>n. (-1)^i * of_nat (n choose i)) = (0 :: 'a::comm_ring_1)"
  by sorry

lemma choose_even_sum:
  assumes "n > 0"
  shows "2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0) = (2 ^ n :: 'a::comm_ring_1)"
  by sorry

lemma choose_odd_sum:
  assumes "n > 0"
  shows "2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0) = (2 ^ n :: 'a::comm_ring_1)"
  by sorry

text\<open>NW diagonal sum property\<close>
lemma sum_choose_diagonal:
  assumes "m \<le> n"
  shows "(\<Sum>k\<le>m. (n - k) choose (m - k)) = Suc n choose m"
  by sorry


subsection \<open>Generalized binomial coefficients\<close>

definition gbinomial :: "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"  (infix \<open>gchoose\<close> 64)
  where gbinomial_prod_rev: "a gchoose k = (\<Prod>i=0..<k. a - of_nat i) div fact k"

lemma gbinomial_0 [simp]:
  "a gchoose 0 = 1"
  "0 gchoose (Suc k) = 0"
  by sorry

lemma gbinomial_Suc: "a gchoose (Suc k) = prod (\<lambda>i. a - of_nat i) {0..k} div fact (Suc k)"
  by sorry

lemma gbinomial_1 [simp]: "a gchoose 1 = a"
  by sorry

lemma gbinomial_Suc0 [simp]: "a gchoose Suc 0 = a"
  by sorry

lemma gbinomial_0_left: "0 gchoose k = (if k = 0 then 1 else 0)"
  by sorry

lemma gbinomial_mult_fact: "fact k * (a gchoose k) = (\<Prod>i = 0..<k. a - of_nat i)"
  for a :: "'a::field_char_0"
  by sorry

lemma gbinomial_mult_fact': "(a gchoose k) * fact k = (\<Prod>i = 0..<k. a - of_nat i)"
  for a :: "'a::field_char_0"
  by sorry

lemma gbinomial_pochhammer: "a gchoose k = (- 1) ^ k * pochhammer (- a) k / fact k"
  for a :: "'a::field_char_0"
  by sorry

lemma gbinomial_pochhammer': "a gchoose k = pochhammer (a - of_nat k + 1) k / fact k"
  for a :: "'a::field_char_0"
  by sorry

lemma gbinomial_binomial: "n gchoose k = n choose k"
  by sorry

lemma of_nat_gbinomial: "of_nat (n gchoose k) = (of_nat n gchoose k :: 'a::field_char_0)"
  by sorry

lemma binomial_gbinomial: "of_nat (n choose k) = (of_nat n gchoose k :: 'a::field_char_0)"
  by sorry

setup
  \<open>Sign.add_const_constraint (\<^const_name>\<open>gbinomial\<close>, SOME \<^typ>\<open>'a::field_char_0 \<Rightarrow> nat \<Rightarrow> 'a\<close>)\<close>

lemma gbinomial_mult_1:
  fixes a :: "'a::field_char_0"
  shows "a * (a gchoose k) = of_nat k * (a gchoose k) + of_nat (Suc k) * (a gchoose (Suc k))"
  (is "?l = ?r")
  by sorry

lemma gbinomial_mult_1':
  "(a gchoose k) * a = of_nat k * (a gchoose k) + of_nat (Suc k) * (a gchoose (Suc k))"
  for a :: "'a::field_char_0"
  by sorry

lemma gbinomial_Suc_Suc: "(a + 1) gchoose (Suc k) = (a gchoose k) + (a gchoose (Suc k))"
  for a :: "'a::field_char_0"
  by sorry

lemma gbinomial_reduce_nat: "0 < k \<Longrightarrow> a gchoose k = (a-1 gchoose k-1) + (a-1 gchoose k)"
  for a :: "'a::field_char_0"
  by sorry

lemma gchoose_row_sum_weighted:
  "(\<Sum>k = 0..m. (r gchoose k) * (r/2 - of_nat k)) = of_nat(Suc m) / 2 * (r gchoose (Suc m))"
  for r :: "'a::field_char_0"
  by sorry

lemma binomial_symmetric:
  assumes kn: "k \<le> n"
  shows "n choose k = n choose (n - k)"
  by sorry

lemma choose_rising_sum:
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))"
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose m)"
  by sorry

lemma choose_linear_sum: "(\<Sum>i\<le>n. i * (n choose i)) = n * 2 ^ (n - 1)"
  by sorry

lemma choose_alternating_linear_sum:
  assumes "n \<noteq> 1"
  shows "(\<Sum>i\<le>n. (-1)^i * of_nat i * of_nat (n choose i) :: 'a::comm_ring_1) = 0"
  by sorry

lemma vandermonde: "(\<Sum>k\<le>r. (m choose k) * (n choose (r - k))) = (m + n) choose r"
  by sorry

lemma choose_square_sum: "(\<Sum>k\<le>n. (n choose k)^2) = ((2*n) choose n)"
  by sorry

lemma pochhammer_binomial_sum:
  fixes a b :: "'a::comm_ring_1"
  shows "pochhammer (a + b) n = (\<Sum>k\<le>n. of_nat (n choose k) * pochhammer a k * pochhammer b (n - k))"
  by sorry

text \<open>Contributed by Manuel Eberl, generalised by LCP.
  Alternative definition of the binomial coefficient as \<^term>\<open>\<Prod>i<k. (n - i) / (k - i)\<close>.\<close>
lemma gbinomial_altdef_of_nat: "a gchoose k = (\<Prod>i = 0..<k. (a - of_nat i) / of_nat (k - i) :: 'a)"
  for k :: nat and a :: "'a::field_char_0"
  by sorry

lemma gbinomial_ge_n_over_k_pow_k:
  fixes k :: nat
    and a :: "'a::linordered_field"
  assumes "of_nat k \<le> a"
  shows "(a / of_nat k :: 'a) ^ k \<le> a gchoose k"
  by sorry

lemma gbinomial_negated_upper: "(a gchoose k) = (-1) ^ k * ((of_nat k - a - 1) gchoose k)"
  by sorry

lemma gbinomial_minus: "((-a) gchoose k) = (-1) ^ k * ((a + of_nat k - 1) gchoose k)"
  by sorry

lemma Suc_times_gbinomial: "of_nat (Suc k) * ((a + 1) gchoose (Suc k)) = (a + 1) * (a gchoose k)"
  by sorry

lemma gbinomial_factors: "((a + 1) gchoose (Suc k)) = (a + 1) / of_nat (Suc k) * (a gchoose k)"
  by sorry

lemma gbinomial_rec: "((a + 1) gchoose (Suc k)) = (a gchoose k) * ((a + 1) / of_nat (Suc k))"
  by sorry

lemma gbinomial_of_nat_symmetric: "k \<le> n \<Longrightarrow> (of_nat n) gchoose k = (of_nat n) gchoose (n - k)"
  by sorry


text \<open>The absorption identity (equation 5.5 \<^cite>\<open>\<open>p.~157\<close> in GKP_CM\<close>):
\[
{r \choose k} = \frac{r}{k}{r - 1 \choose k - 1},\quad \textnormal{integer } k \neq 0.
\]\<close>
lemma gbinomial_absorption': "k > 0 \<Longrightarrow> a gchoose k = (a / of_nat k) * (a - 1 gchoose (k - 1))"
  by sorry

text \<open>The absorption identity is written in the following form to avoid
division by $k$ (the lower index) and therefore remove the $k \neq 0$
restriction \<^cite>\<open>\<open>p.~157\<close> in GKP_CM\<close>:
\[
k{r \choose k} = r{r - 1 \choose k - 1}, \quad \textnormal{integer } k.
\]\<close>
lemma gbinomial_absorption: "of_nat (Suc k) * (a gchoose Suc k) = a * ((a - 1) gchoose k)"
  by sorry

text \<open>The absorption identity for natural number binomial coefficients:\<close>
lemma binomial_absorption: "Suc k * (n choose Suc k) = n * ((n - 1) choose k)"
  by sorry

text \<open>The absorption companion identity for natural number coefficients,
  following the proof by GKP \<^cite>\<open>\<open>p.~157\<close> in GKP_CM\<close>:\<close>
lemma binomial_absorb_comp: "(n - k) * (n choose k) = n * ((n - 1) choose k)"
  (is "?lhs = ?rhs")
  by sorry

text \<open>The generalised absorption companion identity:\<close>
lemma gbinomial_absorb_comp: "(a - of_nat k) * (a gchoose k) = a * ((a - 1) gchoose k)"
  by sorry

lemma gbinomial_addition_formula:
  "a gchoose (Suc k) = ((a - 1) gchoose (Suc k)) + ((a - 1) gchoose k)"
  by sorry

lemma binomial_addition_formula:
  "0 < n \<Longrightarrow> n choose (Suc k) = ((n - 1) choose (Suc k)) + ((n - 1) choose k)"
  by sorry

text \<open>
  Equation 5.9 of the reference material \<^cite>\<open>\<open>p.~159\<close> in GKP_CM\<close> is a useful
  summation formula, operating on both indices:
  \[
   \sum\limits_{k \leq n}{r + k \choose k} = {r + n + 1 \choose n},
   \quad \textnormal{integer } n.
  \]
\<close>
lemma gbinomial_parallel_sum: "(\<Sum>k\<le>n. (a + of_nat k) gchoose k) = (a + of_nat n + 1) gchoose n"
  by sorry


subsection \<open>Summation on the upper index\<close>

text \<open>
  Another summation formula is equation 5.10 of the reference material \<^cite>\<open>\<open>p.~160\<close> in GKP_CM\<close>,
  aptly named \emph{summation on the upper index}:\[\sum_{0 \leq k \leq n} {k \choose m} =
  {n + 1 \choose m + 1}, \quad \textnormal{integers } m, n \geq 0.\]
\<close>
lemma gbinomial_sum_up_index:
  "(\<Sum>j = 0..n. (of_nat j gchoose k) :: 'a::field_char_0) = (of_nat n + 1) gchoose (k + 1)"
  by sorry

lemma gbinomial_index_swap:
  "((-1) ^ k) * ((- (of_nat n) - 1) gchoose k) = ((-1) ^ n) * ((- (of_nat k) - 1) gchoose n)"
  (is "?lhs = ?rhs")
  by sorry

lemma gbinomial_sum_lower_neg: "(\<Sum>k\<le>m. (a gchoose k) * (- 1) ^ k) = (- 1) ^ m * (a - 1 gchoose m)"
  (is "?lhs = ?rhs")
  by sorry

lemma gbinomial_partial_row_sum:
  "(\<Sum>k\<le>m. (a gchoose k) * ((a / 2) - of_nat k)) = ((of_nat m + 1)/2) * (a gchoose (m + 1))"
  by sorry

lemma sum_bounds_lt_plus1: "(\<Sum>k<mm. f (Suc k)) = (\<Sum>k=1..mm. f k)"
  by sorry

lemma gbinomial_partial_sum_poly:
  "(\<Sum>k\<le>m. (of_nat m + a gchoose k) * x^k * y^(m-k)) =
    (\<Sum>k\<le>m. (-a gchoose k) * (-x)^k * (x + y)^(m-k))"
  (is "?lhs m = ?rhs m")
  by sorry

lemma gbinomial_partial_sum_poly_xpos:
    "(\<Sum>k\<le>m. (of_nat m + a gchoose k) * x^k * y^(m-k)) =
     (\<Sum>k\<le>m. (of_nat k + a - 1 gchoose k) * x^k * (x + y)^(m-k))" (is "?lhs = ?rhs")
  by sorry

lemma binomial_r_part_sum: "(\<Sum>k\<le>m. (2 * m + 1 choose k)) = 2 ^ (2 * m)"
  by sorry

lemma gbinomial_r_part_sum: "(\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k)) = 2 ^ (2 * m)"
  (is "?lhs = ?rhs")
  by sorry

lemma gbinomial_sum_nat_pow2:
  "(\<Sum>k\<le>m. (of_nat (m + k) gchoose k :: 'a::field_char_0) / 2 ^ k) = 2 ^ m"
  (is "?lhs = ?rhs")
  by sorry

lemma gbinomial_trinomial_revision:
  assumes "k \<le> m"
  shows "(a gchoose m) * (of_nat m gchoose k) = (a gchoose k) * (a - of_nat k gchoose (m - k))"
  by sorry

text \<open>Versions of the theorems above for the natural-number version of "choose"\<close>
lemma binomial_altdef_of_nat:
  "k \<le> n \<Longrightarrow> of_nat (n choose k) = (\<Prod>i = 0..<k. of_nat (n - i) / of_nat (k - i) :: 'a)"
  for n k :: nat and x :: "'a::field_char_0"
  by sorry

lemma binomial_ge_n_over_k_pow_k: "k \<le> n \<Longrightarrow> (of_nat n / of_nat k :: 'a) ^ k \<le> of_nat (n choose k)"
  for k n :: nat and x :: "'a::linordered_field"
  by sorry

lemma binomial_le_pow:
  assumes "r \<le> n"
  shows "n choose r \<le> n ^ r"
  by sorry

lemma choose_dvd:
  assumes "k \<le> n" shows "fact k * fact (n - k) dvd (fact n)"
  by sorry

lemma fact_fact_dvd_fact:
  "fact k * fact n dvd (fact (k + n))"
  by sorry

lemma choose_mult_lemma:
  "((m + r + k) choose (m + k)) * ((m + k) choose k) = ((m + r + k) choose k) * ((m + r) choose m)"
  (is "?lhs = _")
  by sorry

text \<open>The "Subset of a Subset" identity.\<close>
lemma choose_mult:
  "k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (n choose m) * (m choose k) = (n choose k) * ((n - k) choose (m - k))"
  by sorry

lemma of_nat_binomial_eq_mult_binomial_Suc:
  assumes "k \<le> n"
  shows "(of_nat :: (nat \<Rightarrow> ('a :: field_char_0))) (n choose k) = of_nat (n + 1 - k) / of_nat (n + 1) * of_nat (Suc n choose k)"
  by sorry


subsection \<open>More on Binomial Coefficients\<close>

text \<open>The number of nat lists of length \<open>m\<close> summing to \<open>N\<close> is \<^term>\<open>(N + m - 1) choose N\<close>:\<close>
lemma card_length_sum_list_rec:
  assumes "m \<ge> 1"
  shows "card {l::nat list. length l = m \<and> sum_list l = N} =
      card {l. length l = (m - 1) \<and> sum_list l = N} +
      card {l. length l = m \<and> sum_list l + 1 = N}"
    (is "card ?C = card ?A + card ?B")
  by sorry

lemma card_length_sum_list: "card {l::nat list. size l = m \<and> sum_list l = N} = (N + m - 1) choose N"
  \<comment> \<open>by Holden Lee, tidied by Tobias Nipkow\<close>
  by sorry

lemma card_disjoint_shuffles:
  assumes "set xs \<inter> set ys = {}"
  shows   "card (shuffles xs ys) = (length xs + length ys) choose length xs"
  by sorry

lemma Suc_times_binomial_add: "Suc a * (Suc (a + b) choose Suc a) = Suc b * (Suc (a + b) choose a)"
  \<comment> \<open>by Lukas Bulwahn\<close>
  by sorry

subsection \<open>Inclusion-exclusion principle\<close>

text \<open>Ported from HOL Light by lcp\<close>

lemma Inter_over_Union:
  "\<Inter> {\<Union> (\<F> x) |x. x \<in> S} = \<Union> {\<Inter> (G ` S) |G. \<forall>x\<in>S. G x \<in> \<F> x}" 
  by sorry

lemma subset_insert_lemma:
  "{T. T \<subseteq> (insert a S) \<and> P T} = {T. T \<subseteq> S \<and> P T} \<union> {insert a T |T. T \<subseteq> S \<and> P(insert a T)}" (is "?L=?R")
  by sorry


text\<open>Versions for additive real functions, where the additivity applies only to some
 specific subsets (e.g. cardinality of finite sets, measurable sets with bounded measure.
 (From HOL Light)\<close>

locale Incl_Excl =
  fixes P :: "'a set \<Rightarrow> bool" and f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes disj_add: "\<lbrakk>P S; P T; disjnt S T\<rbrakk> \<Longrightarrow> f(S \<union> T) = f S + f T"
    and empty: "P{}"
    and Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<inter> T)"
    and Un: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<union> T)"
    and Diff: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S - T)"

begin

lemma f_empty [simp]: "f{} = 0"
  by sorry

lemma f_Un_Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> f(S \<union> T) + f(S \<inter> T) = f S + f T"
  by sorry

lemma restricted_indexed:
  assumes "finite A" and X: "\<And>a. a \<in> A \<Longrightarrow> P(X a)"
  shows "f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
  by sorry

lemma restricted:
  assumes "finite A" "\<And>a. a \<in> A \<Longrightarrow> P a"
  shows  "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  by sorry

end

subsection\<open>Versions for unrestrictedly additive functions\<close>

lemma Incl_Excl_UN:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union>(G ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (-1) ^ (card B + 1) * f (\<Inter> (G ` B)))"
  by sorry

lemma Incl_Excl_Union:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  by sorry

text \<open>The famous inclusion-exclusion formula for the cardinality of a union\<close>
lemma int_card_UNION:
  assumes "finite A" "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "int (card (\<Union>A)) = (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  by sorry
