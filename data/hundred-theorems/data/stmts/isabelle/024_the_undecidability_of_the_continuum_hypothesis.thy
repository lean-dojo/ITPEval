section\<open>The main theorem\<close>
theory Forcing_Main
  imports 
  Internal_ZFC_Axioms
  Choice_Axiom
  Ordinals_In_MG
  Succession_Poset

begin

subsection\<open>The generic extension is countable\<close>
(*
\<comment> \<open>Useful missing lemma\<close>
lemma surj_imp_well_ord:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "\<exists>s. well_ord(B,r)" 
*)

definition
  minimum :: "i \<Rightarrow> i \<Rightarrow> i" where
  "minimum(r,B) \<equiv> THE b. b\<in>B \<and> (\<forall>y\<in>B. y \<noteq> b \<longrightarrow> \<langle>b, y\<rangle> \<in> r)"

lemma well_ord_imp_min:
  assumes 
    "well_ord(A,r)" "B \<subseteq> A" "B \<noteq> 0"
  shows 
    "minimum(r,B) \<in> B" 
  by sorry

lemma well_ord_surj_imp_lepoll:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "B \<lesssim> A"
  by sorry

lemma (in forcing_data) surj_nat_MG :
  "\<exists>f. f \<in> surj(nat,M[G])"
  by sorry

lemma (in G_generic) MG_eqpoll_nat: "M[G] \<approx> nat"
  by sorry

subsection\<open>The main result\<close>

theorem extensions_of_ctms:
  assumes 
    "M \<approx> nat" "Transset(M)" "M \<Turnstile> ZF"
  shows 
    "\<exists>N. 
      M \<subseteq> N \<and> N \<approx> nat \<and> Transset(N) \<and> N \<Turnstile> ZF \<and> M\<noteq>N \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      (M, []\<Turnstile> AC \<longrightarrow> N \<Turnstile> ZFC)"
  by sorry

end