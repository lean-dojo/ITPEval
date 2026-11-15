(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q4950096 (thousand-theorems__isabelle__Q4950096), "Bourbaki–Witt theorem":
  every inflationary self-map of a nonempty chain-complete partial order has a
  fixed point. This file contains no proof.
*)

theory Q4950096_bourbaki_witt_theorem
  imports Main
begin

definition q4950096_is_chain :: "'a::order set \<Rightarrow> bool" where
  "q4950096_is_chain C \<longleftrightarrow>
    (\<forall>x\<in>C. \<forall>y\<in>C. x \<le> y \<or> y \<le> x)"

locale q4950096_chain_complete_partial_order =
  fixes cSup :: "'a::order set \<Rightarrow> 'a"
  assumes cSup_upper:
      "\<lbrakk>C \<noteq> {}; q4950096_is_chain C; x \<in> C\<rbrakk>
        \<Longrightarrow> x \<le> cSup C"
    and cSup_least:
      "\<lbrakk>C \<noteq> {}; q4950096_is_chain C;
        \<And>y. y \<in> C \<Longrightarrow> y \<le> x\<rbrakk>
        \<Longrightarrow> cSup C \<le> x"
begin

theorem q4950096_bourbaki_witt:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes inflationary: "\<And>x. x \<le> f x"
  shows "\<exists>x. f x = x"
  sorry

end

end
