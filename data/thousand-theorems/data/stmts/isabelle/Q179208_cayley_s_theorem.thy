(*
  Statement-only formalization of thousand-theorems corpus artifact Q179208
  (thousand-theorems__isabelle__Q179208), "Cayley's theorem": every group
  acting faithfully on an arbitrary type is isomorphic to the image subgroup
  of its induced permutation action. This file contains no proof.
*)

theory Q179208_cayley_s_theorem
  imports Main
begin

definition q179208_action_range ::
    "('g::group_add \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> ('h \<Rightarrow> 'h) set" where
  "q179208_action_range act = range act"

definition q179208_is_permutation_subgroup ::
    "('h \<Rightarrow> 'h) set \<Rightarrow> bool" where
  "q179208_is_permutation_subgroup S \<longleftrightarrow>
    (\<forall>p \<in> S. bij p) \<and>
    id \<in> S \<and>
    (\<forall>p \<in> S. \<forall>q \<in> S. p \<circ> q \<in> S) \<and>
    (\<forall>p \<in> S. \<exists>q \<in> S.
      p \<circ> q = id \<and> q \<circ> p = id)"

definition q179208_isomorphism_onto_action_range ::
    "('g::group_add \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> bool" where
  "q179208_isomorphism_onto_action_range act \<longleftrightarrow>
    q179208_is_permutation_subgroup (q179208_action_range act) \<and>
    bij_betw act UNIV (q179208_action_range act) \<and>
    act 0 = id \<and>
    (\<forall>g h. act (g + h) = act g \<circ> act h)"

theorem cayleys_theorem_for_faithful_action:
  fixes act :: "'g::group_add \<Rightarrow> 'h \<Rightarrow> 'h"
  assumes action_identity: "act 0 = id"
    and action_composition: "\<And>g h. act (g + h) = act g \<circ> act h"
    and faithful: "inj act"
  shows "q179208_isomorphism_onto_action_range act"
  sorry

end
