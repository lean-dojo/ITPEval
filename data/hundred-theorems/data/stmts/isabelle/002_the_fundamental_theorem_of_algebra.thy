(*  Title:      HOL/Computational_Algebra/Fundamental_Theorem_Algebra.thy
    Author:     Amine Chaieb, TU Muenchen
*)

section \<open>Fundamental Theorem of Algebra\<close>

theory Fundamental_Theorem_Algebra
imports Polynomial Complex_Main
begin

subsection \<open>More lemmas about module of complex numbers\<close>

text \<open>The triangle inequality for cmod\<close>

lemma complex_mod_triangle_sub: "cmod w \<le> cmod (w + z) + norm z"
  by sorry


subsection \<open>Basic lemmas about polynomials\<close>

lemma poly_bound_exists:
  fixes p :: "'a::{comm_semiring_0,real_normed_div_algebra} poly"
  shows "\<exists>m. m > 0 \<and> (\<forall>z. norm z \<le> r \<longrightarrow> norm (poly p z) \<le> m)"
  by sorry


text \<open>Offsetting the variable in a polynomial gives another of same degree\<close>

definition offset_poly :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
  where "offset_poly p h = fold_coeffs (\<lambda>a q. smult h q + pCons a q) p 0"

lemma offset_poly_0: "offset_poly 0 h = 0"
  by sorry

lemma offset_poly_pCons:
  "offset_poly (pCons a p) h =
    smult h (offset_poly p h) + pCons a (offset_poly p h)"
  by sorry

lemma offset_poly_single [simp]: "offset_poly [:a:] h = [:a:]"
  by sorry

lemma poly_offset_poly: "poly (offset_poly p h) x = poly p (h + x)"
  by sorry

lemma offset_poly_eq_0_lemma: "smult c p + pCons a p = 0 \<Longrightarrow> p = 0"
  by sorry

lemma offset_poly_eq_0_iff [simp]: "offset_poly p h = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma degree_offset_poly [simp]: "degree (offset_poly p h) = degree p"
  by sorry

definition "psize p = (if p = 0 then 0 else Suc (degree p))"

lemma psize_eq_0_iff [simp]: "psize p = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma poly_offset:
  fixes p :: "'a::comm_ring_1 poly"
  shows "\<exists>q. psize q = psize p \<and> (\<forall>x. poly q x = poly p (a + x))"
  by sorry

text \<open>An alternative useful formulation of completeness of the reals\<close>
lemma real_sup_exists:
  assumes ex: "\<exists>x. P x"
    and bz: "\<exists>z. \<forall>x. P x \<longrightarrow> x < z"
  shows "\<exists>s::real. \<forall>y. (\<exists>x. P x \<and> y < x) \<longleftrightarrow> y < s"
  by sorry


subsection \<open>Fundamental theorem of algebra\<close>

lemma unimodular_reduce_norm:
  assumes md: "cmod z = 1"
  shows "cmod (z + 1) < 1 \<or> cmod (z - 1) < 1 \<or> cmod (z + \<i>) < 1 \<or> cmod (z - \<i>) < 1"
  by sorry

text \<open>Hence we can always reduce modulus of \<open>1 + b z^n\<close> if nonzero\<close>
lemma reduce_poly_simple:
  assumes b: "b \<noteq> 0"
    and n: "n \<noteq> 0"
  shows "\<exists>z. cmod (1 + b * z^n) < 1"
  by sorry

text \<open>Bolzano-Weierstrass type property for closed disc in complex plane.\<close>

lemma metric_bound_lemma: "cmod (x - y) \<le> \<bar>Re x - Re y\<bar> + \<bar>Im x - Im y\<bar>"
  by sorry

lemma Bolzano_Weierstrass_complex_disc:
  assumes r: "\<forall>n. cmod (s n) \<le> r"
  shows "\<exists>f z. strict_mono (f :: nat \<Rightarrow> nat) \<and> (\<forall>e >0. \<exists>N. \<forall>n \<ge> N. cmod (s (f n) - z) < e)"
  by sorry

text \<open>Polynomial is continuous.\<close>

lemma poly_cont:
  fixes p :: "'a::{comm_semiring_0,real_normed_div_algebra} poly"
  assumes ep: "e > 0"
  shows "\<exists>d >0. \<forall>w. 0 < norm (w - z) \<and> norm (w - z) < d \<longrightarrow> norm (poly p w - poly p z) < e"
  by sorry

text \<open>Hence a polynomial attains minimum on a closed disc
  in the complex plane.\<close>
lemma poly_minimum_modulus_disc: "\<exists>z. \<forall>w. cmod w \<le> r \<longrightarrow> cmod (poly p z) \<le> cmod (poly p w)"
  by sorry

text \<open>Nonzero polynomial in z goes to infinity as z does.\<close>

lemma poly_infinity:
  fixes p:: "'a::{comm_semiring_0,real_normed_div_algebra} poly"
  assumes ex: "p \<noteq> 0"
  shows "\<exists>r. \<forall>z. r \<le> norm z \<longrightarrow> d \<le> norm (poly (pCons a p) z)"
  by sorry

text \<open>Hence polynomial's modulus attains its minimum somewhere.\<close>
lemma poly_minimum_modulus: "\<exists>z.\<forall>w. cmod (poly p z) \<le> cmod (poly p w)"
  by sorry

text \<open>Constant function (non-syntactic characterization).\<close>
definition "constant f \<longleftrightarrow> (\<forall>x y. f x = f y)"

lemma nonconstant_length: "\<not> constant (poly p) \<Longrightarrow> psize p \<ge> 2"
  by sorry

lemma poly_replicate_append: "poly (monom 1 n * p) (x::'a::comm_ring_1) = x^n * poly p x"
  by sorry

text \<open>Decomposition of polynomial, skipping zero coefficients after the first.\<close>

lemma poly_decompose_lemma:
  assumes nz: "\<not> (\<forall>z. z \<noteq> 0 \<longrightarrow> poly p z = (0::'a::idom))"
  shows "\<exists>k a q. a \<noteq> 0 \<and> Suc (psize q + k) = psize p \<and> (\<forall>z. poly p z = z^k * poly (pCons a q) z)"
  by sorry

lemma poly_decompose:
  fixes p :: "'a::idom poly"
  assumes nc: "\<not> constant (poly p)"
  shows "\<exists>k a q. a \<noteq> 0 \<and> k \<noteq> 0 \<and>
               psize q + k + 1 = psize p \<and>
              (\<forall>z. poly p z = poly p 0 + z^k * poly (pCons a q) z)" 
  by sorry

text \<open>Fundamental theorem of algebra\<close>

theorem fundamental_theorem_of_algebra:
  assumes nc: "\<not> constant (poly p)"
  shows "\<exists>z::complex. poly p z = 0"
  by sorry

text \<open>Alternative version with a syntactic notion of constant polynomial.\<close>

lemma fundamental_theorem_of_algebra_alt:
  assumes nc: "\<not> (\<exists>a l. a \<noteq> 0 \<and> l = 0 \<and> p = pCons a l)"
  shows "\<exists>z. poly p z = (0::complex)"
  by sorry

subsection \<open>Nullstellensatz, degrees and divisibility of polynomials\<close>

lemma nullstellensatz_lemma:
  fixes p :: "complex poly"
  assumes "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0"
    and "degree p = n"
    and "n \<noteq> 0"
  shows "p dvd (q ^ n)"
  by sorry

lemma nullstellensatz_univariate:
  "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow>
    p dvd (q ^ (degree p)) \<or> (p = 0 \<and> q = 0)"
  by sorry

text \<open>Useful lemma\<close>
lemma constant_degree:
  fixes p :: "'a::{idom,ring_char_0} poly"
  shows "constant (poly p) \<longleftrightarrow> degree p = 0" (is "?lhs = ?rhs")
  by sorry

lemma complex_poly_decompose:
  "smult (lead_coeff p) (\<Prod>z|poly p z = 0. [:-z, 1:] ^ order z p) = (p :: complex poly)"
  by sorry

instance complex :: alg_closed_field
  by standard (use fundamental_theorem_of_algebra constant_degree neq0_conv in blast)

lemma size_proots_complex: "size (proots (p :: complex poly)) = degree p"
  by sorry

lemma complex_poly_decompose_multiset:
  "smult (lead_coeff p) (\<Prod>x\<in>#proots p. [:-x, 1:]) = (p :: complex poly)"
  by sorry

lemma complex_poly_decompose':
  obtains root where "smult (lead_coeff p) (\<Prod>i<degree p. [:-root i, 1:]) = (p :: complex poly)"
  by sorry

lemma complex_poly_decompose_rsquarefree:
  assumes "rsquarefree p"
  shows   "smult (lead_coeff p) (\<Prod>z|poly p z = 0. [:-z, 1:]) = (p :: complex poly)"
  by sorry


text \<open>Arithmetic operations on multivariate polynomials.\<close>

lemma mpoly_base_conv:
  fixes x :: "'a::comm_ring_1"
  shows "0 = poly 0 x" "c = poly [:c:] x" "x = poly [:0,1:] x"
  by sorry

lemma mpoly_norm_conv:
  fixes x :: "'a::comm_ring_1"
  shows "poly [:0:] x = poly 0 x" "poly [:poly 0 y:] x = poly 0 x"
  by sorry

lemma mpoly_sub_conv:
  fixes x :: "'a::comm_ring_1"
  shows "poly p x - poly q x = poly p x + -1 * poly q x"
  by sorry

lemma poly_pad_rule: "poly p x = 0 \<Longrightarrow> poly (pCons 0 p) x = 0"
  by sorry

lemma poly_cancel_eq_conv:
  fixes x :: "'a::field"
  shows "x = 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> y = 0 \<longleftrightarrow> a * y - b * x = 0"
  by sorry

lemma poly_divides_pad_rule:
  fixes p:: "('a::comm_ring_1) poly"
  assumes pq: "p dvd q"
  shows "p dvd (pCons 0 q)"
  by sorry

lemma poly_divides_conv0:
  fixes p:: "'a::field poly"
  assumes lgpq: "degree q < degree p" and lq: "p \<noteq> 0"
  shows "p dvd q \<longleftrightarrow> q = 0"
  by sorry

lemma poly_divides_conv1:
  fixes p :: "'a::field poly"
  assumes a0: "a \<noteq> 0"
    and pp': "p dvd p'"
    and qrp': "smult a q - p' = r"
  shows "p dvd q \<longleftrightarrow> p dvd r"
  by sorry

lemma basic_cqe_conv1:
  "(\<exists>x. poly p x = 0 \<and> poly 0 x \<noteq> 0) \<longleftrightarrow> False"
  "(\<exists>x. poly 0 x \<noteq> 0) \<longleftrightarrow> False"
  "(\<exists>x. poly [:c:] x \<noteq> 0) \<longleftrightarrow> c \<noteq> 0"
  "(\<exists>x. poly 0 x = 0) \<longleftrightarrow> True"
  "(\<exists>x. poly [:c:] x = 0) \<longleftrightarrow> c = 0"
  by sorry

lemma basic_cqe_conv2:
  assumes l: "p \<noteq> 0"
  shows "\<exists>x. poly (pCons a (pCons b p)) x = (0::complex)"
  by sorry

lemma  basic_cqe_conv_2b: "(\<exists>x. poly p x \<noteq> (0::complex)) \<longleftrightarrow> p \<noteq> 0"
  by sorry

lemma basic_cqe_conv3:
  fixes p q :: "complex poly"
  assumes l: "p \<noteq> 0"
  shows "(\<exists>x. poly (pCons a p) x = 0 \<and> poly q x \<noteq> 0) \<longleftrightarrow> \<not> (pCons a p) dvd (q ^ psize p)"
  by sorry

lemma basic_cqe_conv4:
  fixes p q :: "complex poly"
  assumes h: "\<And>x. poly (q ^ n) x = poly r x"
  shows "p dvd (q ^ n) \<longleftrightarrow> p dvd r"
  by sorry

lemma poly_const_conv:
  fixes x :: "'a::comm_ring_1"
  shows "poly [:c:] x = y \<longleftrightarrow> c = y"
  by sorry

end
