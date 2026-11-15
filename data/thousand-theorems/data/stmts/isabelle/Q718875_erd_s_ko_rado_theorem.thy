(*
  Statement-only formalization of Thousand Theorems corpus artifact Q718875
  (thousand-theorems__isabelle__Q718875), "Erdős–Ko–Rado theorem": an
  intersecting family of r-element subsets of Fin n, with r at most n div 2,
  has cardinality at most (n - 1) choose (r - 1). This file contains no proof.
*)

theory Q718875_erd_s_ko_rado_theorem
  imports Main
begin

theorem q718875_erdos_ko_rado:
  fixes n r :: nat
    and A :: "nat set set"
  assumes family_on_carrier: "A \<subseteq> Pow {..<n}"
    and uniform: "\<forall>S \<in> A. card S = r"
    and intersecting: "\<forall>S \<in> A. \<forall>T \<in> A. S \<inter> T \<noteq> {}"
    and at_most_half: "r \<le> n div 2"
  shows "card A \<le> ((n - 1) choose (r - 1))"
  sorry

end
