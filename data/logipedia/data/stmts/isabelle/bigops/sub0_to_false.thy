(*
  Statement-only formalization of Logipedia corpus artifact bigops.sub0_to_false:
  when the target bound of a filtered left-inverse embedding is zero, every
  source predicate entry below its bound is false. This file contains no proof.
*)

theory sub0_to_false
  imports Main
begin

definition sub_hk ::
  "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
where
  "sub_hk h k n1 n2 p1 p2 f1 f2 \<longleftrightarrow>
    (\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow>
      (h i < n2 \<and> p2 (h i) = True) \<and> k (h i) = i)"

theorem sub0_to_false:
  fixes h k :: "nat \<Rightarrow> nat"
    and n1 n2 :: nat
    and p1 p2 :: "nat \<Rightarrow> bool"
    and f1 f2 :: "nat \<Rightarrow> nat"
  assumes "n1 = 0"
    and "sub_hk h k n2 n1 p2 p1 f2 f1"
  shows "\<forall>i. i < n2 \<longrightarrow> p2 i = False"
  sorry

end
