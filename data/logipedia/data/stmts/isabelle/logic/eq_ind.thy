(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_ind,
  catalog title "logic.eq_ind": induction for the module's abstract
  polymorphic equality transports any predicate from an element to every
  equal element. This file contains no proof.
*)

theory eq_ind
  imports Main
begin

consts logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem logic_eq_ind:
  "\<forall>x :: 'a.
    \<forall>P :: 'a \<Rightarrow> bool.
      P x \<longrightarrow>
      (\<forall>y :: 'a. logipedia_logic_eq x y \<longrightarrow> P y)"
  sorry

end
