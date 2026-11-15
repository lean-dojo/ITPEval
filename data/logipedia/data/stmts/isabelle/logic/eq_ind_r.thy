(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_ind_r,
  catalog title "logic.eq_ind_r": right-oriented induction for the module's
  abstract polymorphic equality transports a predicate from a fixed element
  to any element equal to it. This file contains no proof.
*)

theory eq_ind_r
  imports Main
begin

consts logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem logic_eq_ind_r:
  "\<forall>a :: 'a.
    \<forall>P :: 'a \<Rightarrow> bool.
      P a \<longrightarrow>
      (\<forall>x :: 'a. logipedia_logic_eq x a \<longrightarrow> P x)"
  sorry

end
