(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_invert_permut, catalog title
  "permutation.permut_invert_permut": the recursively defined inverse of a
  natural-number function that permutes the initial segment from zero through
  n also permutes that segment. This file contains no proof.
*)

theory permut_invert_permut
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

fun logipedia_invert_permut ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_invert_permut 0 f m = 0"
| "logipedia_invert_permut (Suc n) f m =
    (if m = f (Suc n) then Suc n else logipedia_invert_permut n f m)"

theorem permut_invert_permut:
  fixes f :: "nat \<Rightarrow> nat"
    and n :: nat
  assumes "logipedia_permut f n"
  shows "logipedia_permut (logipedia_invert_permut n f) n"
  sorry

end
