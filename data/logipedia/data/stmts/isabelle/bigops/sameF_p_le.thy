(*
  Statement-only formalization of Logipedia corpus artifact bigops.sameF_p_le:
  predicate-restricted pointwise equality on a natural-number prefix is
  preserved when the prefix bound is decreased. This file contains no proof.
*)

theory sameF_p_le
  imports Main
begin

definition sameF_p ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "sameF_p k p f g \<longleftrightarrow>
    (\<forall>i. i < k \<longrightarrow> p i = True \<longrightarrow> f i = g i)"

theorem sameF_p_le:
  fixes p :: "nat \<Rightarrow> bool"
    and f g :: "nat \<Rightarrow> 'a"
    and n m :: nat
  assumes "n \<le> m"
    and "sameF_p m p f g"
  shows "sameF_p n p f g"
  sorry

end
