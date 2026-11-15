(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.transitive_sub, catalog title "bigops.transitive_sub": transitivity
  of the selected-index embedding relation under composition. The final two
  source parameters are retained even though the source definition does not
  inspect them. This file contains no proof.
*)

theory transitive_sub
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
      (h i < n2 \<and> p2 (h i) = True) \<and>
      k (h i) = i)"

theorem transitive_sub:
  fixes h1 k1 h2 k2 :: "nat \<Rightarrow> nat"
    and n1 n2 n3 :: nat
    and p1 p2 p3 :: "nat \<Rightarrow> bool"
    and f1 f2 f3 :: "nat \<Rightarrow> nat"
  assumes "sub_hk h1 k1 n1 n2 p1 p2 f1 f2"
    and "sub_hk h2 k2 n2 n3 p2 p3 f2 f3"
  shows "sub_hk
    (\<lambda>x. h2 (h1 x))
    (\<lambda>x. k1 (k2 x))
    n1 n3 p1 p3 f1 f3"
  sorry

end
