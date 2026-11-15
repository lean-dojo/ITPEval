(*
  File:       E_Transcendental.thy
  Author:     Manuel Eberl <manuel@pruvisto.org>

  A proof that e (Euler's number) is transcendental.
  Could possibly be extended to a transcendence proof for pi or
  the very general Lindemann-Weierstrass theorem.
*)
section \<open>Proof of the Transcendence of $e$\<close>
theory E_Transcendental
  imports
    "HOL-Complex_Analysis.Complex_Analysis"
    "HOL-Number_Theory.Number_Theory"
    "HOL-Computational_Algebra.Polynomial"
    "Polynomial_Interpolation.Ring_Hom_Poly"
begin

hide_const (open) UnivPoly.coeff  UnivPoly.up_ring.monom 
hide_const (open) Module.smult  Coset.order

subsection \<open>Various auxiliary facts\<close>

lemma fact_dvd_pochhammer:
  assumes "m \<le> n + 1"
  shows   "fact m dvd pochhammer (int n - int m + 1) m"
  by sorry

lemma prime_elem_int_not_dvd_neg1_power:
  "prime_elem (p :: int) \<Longrightarrow> \<not>p dvd (-1) ^ n"
  by sorry

lemma nat_fact [simp]: "nat (fact n) = fact n"
  by sorry

lemma prime_dvd_fact_iff_int:
  "p dvd fact n \<longleftrightarrow> p \<le> int n" if "prime p"
  by sorry

lemma power_over_fact_tendsto_0:
  "(\<lambda>n. (x :: real) ^ n / fact n) \<longlonglongrightarrow> 0"
  by sorry

lemma power_over_fact_tendsto_0':
  "(\<lambda>n. c * (x :: real) ^ n / fact n) \<longlonglongrightarrow> 0"
  by sorry


subsection \<open>General facts about polynomials\<close>

lemma fact_dvd_higher_pderiv:
  "[:fact n :: int:] dvd (pderiv ^^ n) p"
  by sorry

lemma fact_dvd_poly_higher_pderiv_aux:
  "(fact n :: int) dvd poly ((pderiv ^^ n) p) x"
  by sorry

lemma fact_dvd_poly_higher_pderiv_aux':
  "m \<le> n \<Longrightarrow> (fact m :: int) dvd poly ((pderiv ^^ n) p) x"
  by sorry


subsection \<open>Main proof\<close>

lemma lindemann_weierstrass_integral:
  fixes u :: complex and f :: "complex poly"
  defines "df \<equiv> \<lambda>n. (pderiv ^^ n) f"
  defines "m \<equiv> degree f"
  defines "I \<equiv> \<lambda>f u. exp u * (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) 0) -
                       (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) u)"
  shows "((\<lambda>t. exp (u - t) * poly f t) has_contour_integral I f u) (linepath 0 u)"
  by sorry

locale lindemann_weierstrass_aux =
  fixes f :: "complex poly"
begin

definition I :: "complex \<Rightarrow> complex" where
  "I u = exp u * (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) 0) -
                       (\<Sum>j\<le>degree f. poly ((pderiv ^^ j) f) u)"

lemma lindemann_weierstrass_integral_bound:
  fixes u :: complex
  assumes "C \<ge> 0" "\<And>t. t \<in> closed_segment 0 u \<Longrightarrow> norm (poly f t) \<le> C"
  shows "norm (I u) \<le> norm u * exp (norm u) * C"
  by sorry

end

lemma poly_higher_pderiv_aux1:
  fixes c :: "'a :: idom"
  assumes "k < n"
  shows   "poly ((pderiv ^^ k) ([:-c, 1:] ^ n * p)) c = 0"
  by sorry

lemma poly_higher_pderiv_aux1':
  fixes c :: "'a :: idom"
  assumes "k < n" "[:-c, 1:] ^ n dvd p"
  shows   "poly ((pderiv ^^ k) p) c = 0"
  by sorry

lemma poly_higher_pderiv_aux2:
  fixes c :: "'a :: {idom, semiring_char_0}"
  shows   "poly ((pderiv ^^ n) ([:-c, 1:] ^ n * p)) c = fact n * poly p c"
  by sorry

lemma poly_higher_pderiv_aux3:
  fixes c :: "'a :: {idom,semiring_char_0}"
  assumes "k \<ge> n"
  shows   "\<exists>q. poly ((pderiv ^^ k) ([:-c, 1:] ^ n * p)) c = fact n * poly q c"
  by sorry

lemma poly_higher_pderiv_aux3':
  fixes c :: "'a :: {idom, semiring_char_0}"
  assumes "k \<ge> n" "[:-c, 1:] ^ n dvd p"
  shows   "fact n dvd poly ((pderiv ^^ k) p) c"
  by sorry

lemma e_transcendental_aux_bound:
  obtains C where "C \<ge> 0"
    "\<And>x. x \<in> closed_segment 0 (of_nat n) \<Longrightarrow>
        norm (\<Prod>k\<in>{1..n}. (x - of_nat k :: complex)) \<le> C"
  by sorry


theorem e_transcendental_complex: "\<not> algebraic (exp 1 :: complex)"
  by sorry

corollary e_transcendental_real: "\<not> algebraic (exp 1 :: real)"
  by sorry

end
