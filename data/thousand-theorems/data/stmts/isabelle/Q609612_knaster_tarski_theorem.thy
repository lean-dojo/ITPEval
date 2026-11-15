(*
  Statement-only formalization of the thousand-theorems corpus artifact Q609612
  (thousand-theorems__isabelle__Q609612), "Knaster–Tarski theorem": the fixed
  points of a monotone self-map of a complete lattice form a complete lattice
  under the inherited order. This file contains no proof.
*)

theory Q609612_knaster_tarski_theorem
  imports Main
begin

definition q609612_is_lub_in ::
    "'a::order set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "q609612_is_lub_in C S u \<longleftrightarrow>
    u \<in> C \<and>
    (\<forall>x \<in> S. x \<le> u) \<and>
    (\<forall>z \<in> C. (\<forall>x \<in> S. x \<le> z) \<longrightarrow> u \<le> z)"

definition q609612_is_glb_in ::
    "'a::order set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "q609612_is_glb_in C S l \<longleftrightarrow>
    l \<in> C \<and>
    (\<forall>x \<in> S. l \<le> x) \<and>
    (\<forall>z \<in> C. (\<forall>x \<in> S. z \<le> x) \<longrightarrow> z \<le> l)"

theorem q609612_knaster_tarski_theorem:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes monotone: "mono f"
  shows "\<forall>S \<subseteq> {x. f x = x}.
    (\<exists>u. q609612_is_lub_in {x. f x = x} S u) \<and>
    (\<exists>l. q609612_is_glb_in {x. f x = x} S l)"
  sorry

end
