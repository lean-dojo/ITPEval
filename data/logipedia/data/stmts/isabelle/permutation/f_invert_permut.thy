(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.f_invert_permut, catalog title
  "permutation.f_invert_permut": if a natural-number function is a
  permutation of the initial segment through n, then applying it to the
  recursively defined inverse-permutation value of any m in that segment
  returns m. This file contains no proof.
*)

theory f_invert_permut
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

fun logipedia_invert_permut ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_invert_permut 0 f m = 0"
| "logipedia_invert_permut (Suc n) f m =
    (if m = f (Suc n) then Suc n else logipedia_invert_permut n f m)"

theorem f_invert_permut:
  fixes f :: "nat \<Rightarrow> nat"
    and n m :: nat
  assumes "m \<le> n"
    and "logipedia_permut f n"
  shows "f (logipedia_invert_permut n f m) = m"
  sorry

end
