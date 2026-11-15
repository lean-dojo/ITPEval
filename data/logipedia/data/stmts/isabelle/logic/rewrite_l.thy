(*
  Statement-only formalization of Logipedia corpus artifact logic.rewrite_l,
  catalog title "logic.rewrite_l": left-oriented rewriting for the module's
  abstract polymorphic equality transports any predicate from an element to
  every equal element. This file contains no proof.
*)

theory rewrite_l
  imports Main
begin

consts logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem logic_rewrite_l:
  "\<forall>x :: 'a.
    \<forall>P :: 'a \<Rightarrow> bool.
      P x \<longrightarrow>
      (\<forall>y :: 'a. logipedia_logic_eq x y \<longrightarrow> P y)"
  sorry

end
