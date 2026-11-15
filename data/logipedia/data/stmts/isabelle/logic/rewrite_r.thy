(*
  Statement-only formalization of Logipedia corpus artifact logic.rewrite_r,
  catalog title "logic.rewrite_r": right-oriented substitution along
  polymorphic equality transports a predicate from an element to every
  element equal to it. This file contains no proof.
*)

theory rewrite_r
  imports Main
begin

definition logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_logic_eq x y \<longleftrightarrow> x = y"

theorem logic_rewrite_r:
  "\<forall>x :: 'a.
    \<forall>P :: 'a \<Rightarrow> bool.
      P x \<longrightarrow>
      (\<forall>y :: 'a. logipedia_logic_eq y x \<longrightarrow> P y)"
  sorry

end
