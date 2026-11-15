(*
  Statement-only formalization of Logipedia corpus artifact bigops.sub_lt:
  inclusion of a Boolean-filtered natural-number prefix into a larger prefix
  via identity maps satisfies the sub_hk condition. This file contains no proof.
*)

theory sub_lt
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

theorem sub_lt:
  fixes e :: "nat \<Rightarrow> nat"
    and p :: "nat \<Rightarrow> bool"
    and n m :: nat
  assumes "n \<le> m"
  shows "sub_hk (\<lambda>x. x) (\<lambda>x. x) n m p p e e"
  sorry

end
