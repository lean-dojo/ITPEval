(*
  Statement-only formalization of Logipedia corpus artifact logic.sym_eq,
  catalog title "logic.sym_eq": symmetry of the logic module's abstract
  polymorphic equality relation. This file contains no proof.
*)

theory sym_eq
  imports Main
begin

consts logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem logic_sym_eq:
  "\<forall>x :: 'a.
    \<forall>y :: 'a.
      logipedia_logic_eq x y \<longrightarrow> logipedia_logic_eq y x"
  sorry

end
