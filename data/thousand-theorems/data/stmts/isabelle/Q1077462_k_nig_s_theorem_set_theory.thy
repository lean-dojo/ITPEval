(*
  Statement-only formalization of thousand-theorems corpus artifact Q1077462,
  "König's theorem (set theory)": for arbitrary set-indexed families of sets,
  pointwise strict inequality between fiber cardinalities implies that the
  cardinality of their disjoint sum is strictly smaller than that of their
  dependent product.
  This file contains no proof.
*)

theory Q1077462_k_nig_s_theorem_set_theory
  imports "HOL-Cardinals.Cardinal_Arithmetic"
begin

theorem konig_set_theory:
  fixes I :: "'i set"
    and F :: "'i \<Rightarrow> 'a set"
    and G :: "'i \<Rightarrow> 'b set"
  assumes pointwise: "\<And>i. i \<in> I \<Longrightarrow> |F i| <o |G i|"
  shows "|SIGMA i : I. F i| <o |PiE I G|"
  sorry

end
