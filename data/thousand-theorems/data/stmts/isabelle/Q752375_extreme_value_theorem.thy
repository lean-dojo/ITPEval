(*
  Statement-only formalization of the thousand-theorems corpus artifact Q752375,
  "Extreme value theorem": a continuous function from a nonempty compact set
  into a linearly ordered topological space whose lower intervals are closed
  attains its minimum on that set. This file contains no proof.
*)

theory Q752375_extreme_value_theorem
  imports "HOL.Topological_Spaces"
begin

theorem q752375_extreme_value_theorem:
  fixes s :: "'b::topological_space set"
    and f :: "'b \<Rightarrow> 'a::{linorder,topological_space}"
  assumes closed_lower_intervals: "\<And>a. closed {..a}"
    and compact_s: "compact s"
    and nonempty_s: "s \<noteq> {}"
    and continuous_f: "continuous_on s f"
  shows "\<exists>x \<in> s. \<forall>y \<in> s. f x \<le> f y"
  sorry

end
