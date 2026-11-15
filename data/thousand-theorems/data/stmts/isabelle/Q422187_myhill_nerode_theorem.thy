(*
  Statement-only formalization of the thousand-theorems corpus artifact Q422187,
  "Myhill–Nerode theorem": a language over an arbitrary alphabet is regular if
  and only if it has finitely many distinct left quotients. This file contains
  no proof.
*)

theory Q422187_myhill_nerode_theorem
  imports Main
begin

record 'a q422187_dfa =
  q422187_state_count :: nat
  q422187_start :: nat
  q422187_step :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
  q422187_accepting :: "nat set"

definition q422187_well_formed :: "'a q422187_dfa \<Rightarrow> bool" where
  "q422187_well_formed M \<longleftrightarrow>
    q422187_start M < q422187_state_count M \<and>
    q422187_accepting M \<subseteq> {..<q422187_state_count M} \<and>
    (\<forall>q < q422187_state_count M. \<forall>a.
      q422187_step M q a < q422187_state_count M)"

definition q422187_eval :: "'a q422187_dfa \<Rightarrow> 'a list \<Rightarrow> nat" where
  "q422187_eval M w =
    foldl (q422187_step M) (q422187_start M) w"

definition q422187_accepts :: "'a q422187_dfa \<Rightarrow> 'a list set" where
  "q422187_accepts M =
    {w. q422187_eval M w \<in> q422187_accepting M}"

definition q422187_regular :: "'a list set \<Rightarrow> bool" where
  "q422187_regular L \<longleftrightarrow>
    (\<exists>M :: 'a q422187_dfa.
      q422187_well_formed M \<and> q422187_accepts M = L)"

definition q422187_left_quotient ::
    "'a list set \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
  "q422187_left_quotient L x = {y. x @ y \<in> L}"

theorem q422187_myhill_nerode_theorem:
  fixes L :: "'a list set"
  shows "q422187_regular L \<longleftrightarrow>
    finite (range (q422187_left_quotient L))"
  sorry

end
