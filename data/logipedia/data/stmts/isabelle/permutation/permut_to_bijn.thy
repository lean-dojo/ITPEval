(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_to_bijn, catalog title "permutation.permut_to_bijn":
  every natural-number function that maps the initial segment from zero
  through n into itself and is injective there is surjective on that segment.
  This file contains no proof.
*)

theory permut_to_bijn
  imports Main
begin

definition logipedia_injn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_injn f n \<longleftrightarrow>
      (\<forall>i j :: nat.
        i \<le> n \<longrightarrow> j \<le> n \<longrightarrow>
        f i = f j \<longrightarrow> i = j)"

definition logipedia_permut :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_permut f n \<longleftrightarrow>
      (\<forall>i :: nat. i \<le> n \<longrightarrow> f i \<le> n) \<and>
      logipedia_injn f n"

definition logipedia_bijn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_bijn f n \<longleftrightarrow>
      (\<forall>m :: nat. m \<le> n \<longrightarrow>
        (\<exists>p :: nat. p \<le> n \<and> f p = m))"

theorem permut_to_bijn:
  fixes n :: nat
    and f :: "nat \<Rightarrow> nat"
  assumes "logipedia_permut f n"
  shows "logipedia_bijn f n"
  sorry

end
