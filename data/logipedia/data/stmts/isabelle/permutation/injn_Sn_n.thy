(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injn_Sn_n, catalog title "permutation.injn_Sn_n": injectivity
  of a natural-number function on the initial segment through Suc n implies
  injectivity on the initial segment through n. This file contains no proof.
*)

theory injn_Sn_n
  imports Main
begin

definition logipedia_injn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_injn f n \<longleftrightarrow>
    (\<forall>i j :: nat.
      i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> f i = f j \<longrightarrow> i = j)"

theorem injn_Sn_n:
  fixes f :: "nat \<Rightarrow> nat"
    and n :: nat
  assumes "logipedia_injn f (Suc n)"
  shows "logipedia_injn f n"
  sorry

end
