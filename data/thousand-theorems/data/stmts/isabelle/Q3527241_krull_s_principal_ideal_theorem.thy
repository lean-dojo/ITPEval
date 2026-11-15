(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527241
  (thousand-theorems__isabelle__Q3527241), "Krull's principal ideal theorem":
  in a commutative Noetherian ring, a prime ideal minimal over a principal
  ideal has height at most one. This file contains no proof.
*)

theory Q3527241_krull_s_principal_ideal_theorem
  imports "HOL-Algebra.Ideal"
begin

definition q3527241_is_noetherian_ring ::
    "('a, 'b) ring_scheme \<Rightarrow> bool" where
  "q3527241_is_noetherian_ring R \<longleftrightarrow>
    (\<forall>J. ideal J R \<longrightarrow>
      (\<exists>A \<subseteq> carrier R. finite A \<and> J = Idl\<^bsub>R\<^esub> A))"

definition q3527241_minimal_prime_over ::
    "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q3527241_minimal_prime_over R I p \<longleftrightarrow>
    primeideal p R \<and>
    I \<subseteq> p \<and>
    (\<forall>q. primeideal q R \<and> I \<subseteq> q \<and> q \<subseteq> p
      \<longrightarrow> p \<subseteq> q)"

definition q3527241_prime_height_at_most_one ::
    "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q3527241_prime_height_at_most_one R p \<longleftrightarrow>
    \<not> (\<exists>q r.
      primeideal q R \<and>
      primeideal r R \<and>
      q \<subset> r \<and>
      r \<subset> p)"

theorem q3527241_krull_principal_ideal:
  fixes R :: "('a, 'b) ring_scheme"
    and I p :: "'a set"
  assumes "cring R"
    and "q3527241_is_noetherian_ring R"
    and "principalideal I R"
    and "q3527241_minimal_prime_over R I p"
  shows "q3527241_prime_height_at_most_one R p"
  sorry

end
