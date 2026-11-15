(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_S_to_permut_transpose, catalog title
  "permutation.permut_S_to_permut_transpose": a permutation of the natural
  segment through Suc m remains a permutation through m after its values
  f (Suc m) and Suc m are transposed. This file contains no proof.
*)

theory permut_S_to_permut_transpose
  imports Main
begin

definition logipedia_injn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_injn f n \<longleftrightarrow>
    (\<forall>i j :: nat.
      i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> f i = f j \<longrightarrow> i = j)"

definition logipedia_permut :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_permut f n \<longleftrightarrow>
    (\<forall>i :: nat. i \<le> n \<longrightarrow> f i \<le> n) \<and>
    logipedia_injn f n"

definition logipedia_transpose :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_transpose i j n =
    (if n = i then j else if n = j then i else n)"

theorem permut_S_to_permut_transpose:
  fixes f :: "nat \<Rightarrow> nat"
    and m :: nat
  assumes "logipedia_permut f (Suc m)"
  shows
    "logipedia_permut
      (\<lambda>n. logipedia_transpose (f (Suc m)) (Suc m) (f n))
      m"
  sorry

end
