(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q720469 (thousand-theorems__isabelle__Q720469), "Chevalley–Warning theorem":
  for a finite family of multivariate polynomials over a finite field, if the
  sum of their total degrees is less than the number of variables, then the
  field characteristic divides the number of common zeros. This file contains
  no proof.
*)

theory Q720469_chevalley_warning_theorem
  imports Main
begin

type_synonym ('v, 'a) q720469_raw_mpoly = "('v \<Rightarrow> nat) \<Rightarrow> 'a"

definition q720469_monomial_support ::
    "('v \<Rightarrow> nat) \<Rightarrow> 'v set" where
  "q720469_monomial_support m = {v. m v \<noteq> 0}"

definition q720469_polynomial_support ::
    "('v, 'a::zero) q720469_raw_mpoly \<Rightarrow> ('v \<Rightarrow> nat) set" where
  "q720469_polynomial_support f = {m. f m \<noteq> 0}"

definition q720469_is_mpoly ::
    "'v set \<Rightarrow> ('v, 'a::zero) q720469_raw_mpoly \<Rightarrow> bool" where
  "q720469_is_mpoly V f \<longleftrightarrow>
    finite (q720469_polynomial_support f) \<and>
    (\<forall>m\<in>q720469_polynomial_support f.
      finite (q720469_monomial_support m) \<and>
      q720469_monomial_support m \<subseteq> V)"

definition q720469_total_degree ::
    "('v, 'a::zero) q720469_raw_mpoly \<Rightarrow> nat" where
  "q720469_total_degree f =
    (if q720469_polynomial_support f = {} then 0
     else Max ((\<lambda>m. \<Sum>v\<in>q720469_monomial_support m. m v) `
       q720469_polynomial_support f))"

definition q720469_mpoly_eval ::
    "('v \<Rightarrow> 'a::comm_semiring_1) \<Rightarrow>
      ('v, 'a) q720469_raw_mpoly \<Rightarrow> 'a" where
  "q720469_mpoly_eval x f =
    (\<Sum>m\<in>q720469_polynomial_support f.
      f m * (\<Prod>v\<in>q720469_monomial_support m. x v ^ m v))"

theorem char_dvd_card_solutions_of_sum_lt:
  fixes V :: "'v set"
    and s :: "'i set"
    and f :: "'i \<Rightarrow> ('v, 'K::{finite,field}) q720469_raw_mpoly"
    and p :: nat
  assumes finite_V: "finite V"
    and finite_s: "finite s"
    and polynomial_f: "\<forall>i. q720469_is_mpoly V (f i)"
    and characteristic: "p = CHAR('K)"
    and degree_sum_lt:
      "(\<Sum>i\<in>s. q720469_total_degree (f i)) < card V"
  shows
    "p dvd card
      {x :: 'v \<Rightarrow> 'K.
        (\<forall>v. v \<notin> V \<longrightarrow> x v = 0) \<and>
        (\<forall>i\<in>s. q720469_mpoly_eval x (f i) = 0)}"
  sorry

end
