(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_transpose, catalog title "permutation.bijn_transpose":
  transposing two bounded natural-number positions is surjective on the
  initial segment through the bound. This file contains no proof.
*)

theory bijn_transpose
  imports Main
begin

definition transpose :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "transpose i j k = (if k = i then j else if k = j then i else k)"

definition bijn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "bijn f n \<longleftrightarrow>
    (\<forall>m :: nat. m \<le> n \<longrightarrow>
      (\<exists>p :: nat. p \<le> n \<and> f p = m))"

theorem bijn_transpose:
  "\<forall>n i j :: nat.
    i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> bijn (transpose i j) n"
  sorry

end
