(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_n_Sn, catalog title "permutation.bijn_n_Sn": if a function
  is surjective on the natural-number segment from 0 through n using
  preimages in that segment and fixes Suc n, then it is surjective on the
  segment from 0 through Suc n. This file contains no proof.
*)

theory bijn_n_Sn
  imports Main
begin

definition logipedia_bijn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_bijn f n \<longleftrightarrow>
      (\<forall>m. m \<le> n \<longrightarrow> (\<exists>p. p \<le> n \<and> f p = m))"

theorem bijn_n_Sn:
  fixes f :: "nat \<Rightarrow> nat"
    and n :: nat
  assumes "logipedia_bijn f n"
    and "f (Suc n) = Suc n"
  shows "logipedia_bijn f (Suc n)"
  sorry

end
