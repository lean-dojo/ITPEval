(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_rect_r,
  catalog title "logic.eq_rect_r": right-oriented transport for the logic
  module's abstract polymorphic equality sends any predicate holding at a to x
  when x is equal to a. This file contains no proof.
*)

theory eq_rect_r
  imports Main
begin

consts logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

theorem logic_eq_rect_r:
  "\<forall>a x :: 'a.
    logipedia_logic_eq x a \<longrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P a \<longrightarrow> P x)"
  sorry

end
