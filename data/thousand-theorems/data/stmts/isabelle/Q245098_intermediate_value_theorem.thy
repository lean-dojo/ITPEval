(*
  Statement-only formalization of the thousand-theorems corpus artifact Q245098,
  "Intermediate value theorem": a continuous map on a closed interval in a
  densely ordered conditionally complete linear order attains every value
  between its endpoint values. This file contains no proof.
*)

theory Q245098_intermediate_value_theorem
  imports "HOL.Topological_Spaces"
begin

theorem q245098_intermediate_value_Icc:
  fixes a b :: "'a::{conditionally_complete_linorder,dense_linorder,linorder_topology}"
    and f :: "'a \<Rightarrow> 'b::{linorder,topological_space}"
  assumes "a \<le> b"
    and "closed ({(x, y). x \<le> y} :: ('b \<times> 'b) set)"
    and "continuous_on {a..b} f"
  shows "{f a..f b} \<subseteq> f ` {a..b}"
  sorry

end
