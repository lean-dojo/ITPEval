(*
  Statement-only formalization of thousand-theorems corpus artifact Q716171
  (thousand-theorems__isabelle__Q716171), "Erdős–Ginzburg–Ziv theorem":
  any finite set of at least 2 * n - 1 indices labeled modulo n contains an
  n-element subset whose labels sum to zero modulo n. This file contains no
  proof.
*)

theory Q716171_erd_s_ginzburg_ziv_theorem
  imports Main
begin

theorem erdos_ginzburg_ziv:
  fixes n :: nat
    and s :: "'i set"
    and a :: "'i \<Rightarrow> int"
  assumes finite_s: "finite s"
    and large_s: "2 * n - 1 \<le> card s"
  shows "\<exists>t \<subseteq> s.
    card t = n \<and> (int n) dvd (\<Sum>i\<in>t. a i)"
  sorry

end
