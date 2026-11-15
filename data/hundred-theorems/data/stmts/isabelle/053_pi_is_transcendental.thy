(*
    File:      Pi_Transcendendtal.thy
    Author:    Manuel Eberl, TU München

   A proof of the transcendence of pi
*)
section \<open>The Transcendence of $\pi$\<close>
theory Pi_Transcendental
imports
  "E_Transcendental.E_Transcendental"
  "Symmetric_Polynomials.Symmetric_Polynomials"
  "HOL-Real_Asymp.Real_Asymp" 
begin

lemma ring_homomorphism_to_poly [intro]: "ring_homomorphism (\<lambda>i. [:i:])"
  by sorry

lemma (in ring_closed) coeff_power_closed:
  "(\<And>m. coeff p m \<in> A) \<Longrightarrow> coeff (p ^ n) m \<in> A"
  by sorry

lemma (in ring_closed) coeff_prod_closed:
  "(\<And>x m. x \<in> X \<Longrightarrow> coeff (f x) m \<in> A) \<Longrightarrow> coeff (prod f X) m \<in> A"
  by sorry

lemma map_of_rat_of_int_poly [simp]: "map_poly of_rat (of_int_poly p) = of_int_poly p"
  by sorry

text \<open>
  Given a polynomial with rational coefficients, we can obtain an integer polynomial that
  differs from it only by a nonzero constant by clearing the denominators.
\<close>
lemma ratpoly_to_intpoly:
  assumes "\<forall>i. poly.coeff p i \<in> \<rat>"
  obtains q c where "c \<noteq> 0" "p = Polynomial.smult (inverse (of_nat c)) (of_int_poly q)"
  by sorry

lemma symmetric_mpoly_symmetric_sum:
  assumes "\<And>\<pi>. \<pi> permutes A \<Longrightarrow> g \<pi> permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g \<pi> x)"
  shows "symmetric_mpoly A (\<Sum>x\<in>X. f x)"
  by sorry

(* TODO: The version of this theorem in the AFP is to weak and should be replaced by this one. *)
lemma symmetric_mpoly_symmetric_prod:
  assumes "g permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g x)"
  shows "symmetric_mpoly A (\<Prod>x\<in>X. f x)"
  by sorry


text \<open>
  We now prove the transcendence of $i\pi$, from which the transcendence of $\pi$ will follow
  as a trivial corollary. The first proof of this was given by von Lindemann~\<^cite>\<open>"lindemann_pi82"\<close>.
  The central ingredient is the fundamental theorem of symmetric functions.

  The proof can, by now, be considered folklore and one can easily find many similar variants of
  it, but we mostly follows the nice exposition given by Niven~\<^cite>\<open>"niven_pi39"\<close>.

  An independent previous formalisation in Coq that uses the same basic techniques was given by
  Bernard et al.~\<^cite>\<open>"bernard_pi16"\<close>. They later also formalised the much stronger
  Lindemann--Weierstra{\ss} theorem~\<^cite>\<open>"bernard_lw17"\<close>.
\<close>
lemma transcendental_i_pi: "\<not>algebraic (\<i> * pi)"
  by sorry

lemma pcompose_conjugates_integer:
  assumes "\<And>i. poly.coeff p i \<in> \<int>"
  shows   "poly.coeff (pcompose p [:0, \<i>:] * pcompose p [:0, -\<i>:]) i \<in> \<int>"
  by sorry

lemma algebraic_times_i:
  assumes "algebraic x"
  shows   "algebraic (\<i> * x)" "algebraic (-\<i> * x)"
  by sorry

lemma algebraic_times_i_iff: "algebraic (\<i> * x) \<longleftrightarrow> algebraic x"
  by sorry

theorem transcendental_pi: "\<not>algebraic pi"
  by sorry

end