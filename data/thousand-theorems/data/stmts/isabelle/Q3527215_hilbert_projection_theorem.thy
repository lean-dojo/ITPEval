(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527215
  (thousand-theorems__isabelle__Q3527215), "Hilbert projection theorem":
  every point in a real inner-product space has a nearest point in any
  nonempty complete convex subset. This file contains no proof.
*)

theory Q3527215_hilbert_projection_theorem
  imports "HOL-Analysis.Inner_Product"
begin

theorem exists_norm_eq_Inf_of_complete_convex:
  fixes K :: "'a::real_inner set"
  assumes nonempty: "K \<noteq> {}"
    and complete: "complete K"
    and convex: "convex K"
  shows "\<forall>u::'a. \<exists>v\<in>K.
    norm (u - v) = Inf ((\<lambda>w. norm (u - w)) ` K)"
  sorry

end
