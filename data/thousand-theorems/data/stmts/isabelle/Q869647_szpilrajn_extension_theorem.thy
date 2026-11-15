(*
  Statement-only formalization of the thousand-theorems corpus artifact Q869647
  (thousand-theorems__isabelle__Q869647), "Szpilrajn extension theorem": every
  partial order on an arbitrary, possibly empty carrier extends to a linear
  order on the same carrier. This file contains no proof.
*)

theory Q869647_szpilrajn_extension_theorem
  imports Main
begin

definition q869647_is_partial_order ::
    "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "q869647_is_partial_order A r \<longleftrightarrow>
    r \<subseteq> A \<times> A \<and>
    (\<forall>x\<in>A. (x, x) \<in> r) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
      (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>A.
      (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"

definition q869647_is_linear_order ::
    "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "q869647_is_linear_order A r \<longleftrightarrow>
    q869647_is_partial_order A r \<and>
    (\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> r \<or> (y, x) \<in> r)"

theorem q869647_szpilrajn_extension:
  assumes "q869647_is_partial_order A r"
  shows "\<exists>s. q869647_is_linear_order A s \<and> r \<subseteq> s"
  sorry

end
