(*
  Statement-only formalization of Logipedia corpus artifact bigops.sameF_upto_le:
  pointwise equality of two natural-indexed functions on an initial segment is
  preserved when the segment bound is decreased. This file contains no proof.
*)

theory sameF_upto_le
  imports Main
begin

definition sameF_upto ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "sameF_upto k f g \<longleftrightarrow>
    (\<forall>i. i < k \<longrightarrow> f i = g i)"

theorem sameF_upto_le:
  fixes f g :: "nat \<Rightarrow> 'a"
    and n m :: nat
  assumes "n \<le> m"
    and "sameF_upto m f g"
  shows "sameF_upto n f g"
  sorry

end
