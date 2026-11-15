(*
  Statement-only formalization of Logipedia corpus artifact logic.refl,
  catalog title "logic.refl": reflexivity of the logic module's abstract
  polymorphic equality for every element of every type. This file contains
  no proof.
*)

theory refl
  imports Main
begin

consts logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem logic_refl:
  "\<forall>x :: 'a. logipedia_logic_eq x x"
  sorry

end
