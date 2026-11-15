(*
  Statement-only formalization of Logipedia corpus artifact bigops.sub_hkO:
  a zero source bound makes the filtered left-inverse embedding condition
  sub_hk hold for arbitrary natural-number maps. This file contains no proof.
*)

theory sub_hkO
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

theorem sub_hkO:
  fixes h k :: "nat \<Rightarrow> nat"
    and n1 n2 :: nat
    and p1 p2 :: "nat \<Rightarrow> bool"
    and f1 f2 :: "nat \<Rightarrow> nat"
  assumes "n1 = 0"
  shows "sub_hk h k n1 n2 p1 p2 f1 f2"
  sorry

end
