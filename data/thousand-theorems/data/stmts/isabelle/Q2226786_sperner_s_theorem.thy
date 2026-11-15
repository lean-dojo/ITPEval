(*
  Statement-only formalization of thousand-theorems corpus artifact Q2226786,
  "Sperner's theorem": an inclusion antichain of subsets of a finite carrier,
  which may be empty, has cardinality at most the middle binomial coefficient.
  This file contains no proof.
*)

theory Q2226786_sperner_s_theorem
  imports Main
begin

theorem q2226786_sperner:
  fixes U :: "'a set"
    and A :: "'a set set"
  assumes finite_carrier: "finite U"
    and family_on_carrier: "A \<subseteq> Pow U"
    and antichain:
    "\<And>S T. S \<in> A \<Longrightarrow> T \<in> A \<Longrightarrow>
      S \<subseteq> T \<Longrightarrow> S = T"
  shows
    "card A \<le> (card U choose (card U div 2))"
  sorry

end
