(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q918099 (thousand-theorems__isabelle__Q918099), "Ramsey's theorem": every
  coloring of the finite r-element subsets of an infinite set of natural
  numbers by finitely many colors has an infinite monochromatic subset. This
  file contains no proof.
*)

theory Q918099_ramsey_s_theorem
  imports Main
begin

definition q918099_r_edges :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set" where
  "q918099_r_edges r M =
    {e. finite e \<and> card e = r \<and> e \<subseteq> M}"

theorem ramsey_r:
  fixes K :: "'a set"
    and r :: nat
    and M1 :: "nat set"
    and c :: "nat set \<Rightarrow> 'a"
  assumes finite_K: "finite K"
    and infinite_M1: "infinite M1"
    and colors_in_K:
      "\<And>e. e \<in> q918099_r_edges r M1 \<Longrightarrow> c e \<in> K"
  shows "\<exists>M2. M2 \<subseteq> M1 \<and> infinite M2 \<and>
    (\<exists>col\<in>K. \<forall>e\<in>q918099_r_edges r M2. c e = col)"
  sorry

end
