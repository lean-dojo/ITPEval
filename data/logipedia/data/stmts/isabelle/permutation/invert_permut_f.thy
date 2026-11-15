(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.invert_permut_f, catalog title
  "permutation.invert_permut_f": a natural-number function that is injective
  on the initial segment through n is recovered there by the recursively
  defined inverse-permutation function. This file contains no proof.
*)

theory invert_permut_f
  imports Main
begin

definition logipedia_injn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_injn f n \<longleftrightarrow>
    (\<forall>i j :: nat.
      i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> f i = f j \<longrightarrow> i = j)"

fun logipedia_invert_permut ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_invert_permut 0 f m = 0"
| "logipedia_invert_permut (Suc n) f m =
    (if m = f (Suc n) then Suc n else logipedia_invert_permut n f m)"

theorem invert_permut_f:
  fixes f :: "nat \<Rightarrow> nat"
    and n m :: nat
  assumes "m \<le> n"
    and "logipedia_injn f n"
  shows "logipedia_invert_permut n f (f m) = m"
  sorry

end
