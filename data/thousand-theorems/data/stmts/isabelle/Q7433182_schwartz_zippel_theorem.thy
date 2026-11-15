(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q7433182 (thousand-theorems__isabelle__Q7433182), "Schwartz–Zippel theorem":
  for a nonzero multivariate polynomial over an integral domain, the fraction
  of zeros in a product of coordinate-specific finite sets is bounded by the
  maximum, over supported monomials, of the sum of coordinate degrees divided
  by the corresponding set cardinalities. This file contains no proof.
*)

theory Q7433182_schwartz_zippel_theorem
  imports Complex_Main
begin

type_synonym ('v, 'a) q7433182_raw_mpoly = "('v \<Rightarrow> nat) \<Rightarrow> 'a"

definition q7433182_monomial_support ::
    "('v \<Rightarrow> nat) \<Rightarrow> 'v set" where
  "q7433182_monomial_support m = {i. m i \<noteq> 0}"

definition q7433182_polynomial_support ::
    "('v, 'a::zero) q7433182_raw_mpoly \<Rightarrow> ('v \<Rightarrow> nat) set" where
  "q7433182_polynomial_support p = {m. p m \<noteq> 0}"

definition q7433182_is_mpoly ::
    "('v, 'a::zero) q7433182_raw_mpoly \<Rightarrow> bool" where
  "q7433182_is_mpoly p \<longleftrightarrow>
    finite (q7433182_polynomial_support p) \<and>
    (\<forall>m\<in>q7433182_polynomial_support p.
      finite (q7433182_monomial_support m))"

definition q7433182_mpoly_eval ::
    "('v \<Rightarrow> 'a::comm_semiring_1) \<Rightarrow>
      ('v, 'a) q7433182_raw_mpoly \<Rightarrow> 'a" where
  "q7433182_mpoly_eval x p =
    (\<Sum>m\<in>q7433182_polynomial_support p.
      p m * (\<Prod>i\<in>q7433182_monomial_support m. x i ^ m i))"

definition q7433182_zero_ratio ::
    "('v::finite, 'a::comm_semiring_1) q7433182_raw_mpoly \<Rightarrow>
      ('v \<Rightarrow> 'a set) \<Rightarrow> rat" where
  "q7433182_zero_ratio p S =
    of_nat (card {x. (\<forall>i. x i \<in> S i) \<and>
      q7433182_mpoly_eval x p = 0}) /
      prod (\<lambda>i. of_nat (card (S i))) UNIV"

definition q7433182_monomial_score ::
    "('v::finite \<Rightarrow> 'a set) \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> rat" where
  "q7433182_monomial_score S m =
    sum (\<lambda>i. of_nat (m i) / of_nat (card (S i))) UNIV"

definition q7433182_support_sup ::
    "('v::finite, 'a::zero) q7433182_raw_mpoly \<Rightarrow>
      ('v \<Rightarrow> 'a set) \<Rightarrow> rat" where
  "q7433182_support_sup p S =
    (if q7433182_polynomial_support p = {} then 0
     else Max (q7433182_monomial_score S `
       q7433182_polynomial_support p))"

theorem q7433182_schwartz_zippel_sup_sum:
  fixes p :: "('v::finite, 'a::idom) q7433182_raw_mpoly"
    and S :: "'v \<Rightarrow> 'a set"
  assumes polynomial_p: "q7433182_is_mpoly p"
    and nonzero_p: "p \<noteq> (\<lambda>_. 0)"
    and finite_S: "\<forall>i. finite (S i)"
  shows "q7433182_zero_ratio p S \<le> q7433182_support_sup p S"
  sorry

end
