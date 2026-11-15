(*
  Statement-only formalization of thousand-theorems corpus artifact Q656645
  (thousand-theorems__isabelle__Q656645), "Hilbert's basis theorem": the
  univariate polynomial ring over a commutative Noetherian ring is itself
  Noetherian. This file contains no proof.
*)

theory Q656645_hilbert_s_basis_theorem
  imports "HOL-Algebra.UnivPoly"
begin

definition q656645_is_noetherian_ring ::
    "('a, 'b) ring_scheme \<Rightarrow> bool" where
  "q656645_is_noetherian_ring R \<longleftrightarrow>
    (\<forall>J. ideal J R \<longrightarrow>
      (\<exists>A \<subseteq> carrier R. finite A \<and> J = Idl\<^bsub>R\<^esub> A))"

theorem q656645_hilbert_basis_theorem:
  fixes R :: "('a, 'b) ring_scheme"
  assumes "cring R"
    and "q656645_is_noetherian_ring R"
  shows "q656645_is_noetherian_ring (UP R)"
  sorry

end
