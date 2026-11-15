(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1134776,
  "Dilworth's theorem": in a finite partial order, the minimum cardinality of a
  partition into chains equals the maximum cardinality of an antichain. This file
  contains no proof.
*)

theory Q1134776_dilworth_s_theorem
  imports Main
begin

definition q1134776_is_chain :: "'a::order set \<Rightarrow> bool" where
  "q1134776_is_chain C \<longleftrightarrow>
    (\<forall>x\<in>C. \<forall>y\<in>C. x \<le> y \<or> y \<le> x)"

definition q1134776_is_antichain :: "'a::order set \<Rightarrow> bool" where
  "q1134776_is_antichain A \<longleftrightarrow>
    (\<forall>x\<in>A. \<forall>y\<in>A. x \<le> y \<longrightarrow> x = y)"

definition q1134776_is_chain_partition ::
    "'a::order set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "q1134776_is_chain_partition U P \<longleftrightarrow>
    (\<forall>x\<in>U. \<exists>!C. C \<in> P \<and> x \<in> C) \<and>
    (\<forall>C\<in>P. C \<subseteq> U \<and> q1134776_is_chain C)"

definition q1134776_min_chain_partition ::
    "'a::order set \<Rightarrow> nat" where
  "q1134776_min_chain_partition U =
    Min (card ` {P. q1134776_is_chain_partition U P})"

definition q1134776_antichain_width ::
    "'a::order set \<Rightarrow> nat" where
  "q1134776_antichain_width U =
    Max (card ` {A. A \<subseteq> U \<and> q1134776_is_antichain A})"

theorem q1134776_dilworth:
  "q1134776_min_chain_partition (UNIV :: 'a::{finite,order} set) =
    q1134776_antichain_width UNIV"
  sorry

end
