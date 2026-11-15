(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_f,
  catalog title "logic.eq_f": function application preserves equality between
  elements of an arbitrary source type in an arbitrary target type. This file
  contains no proof.
*)

theory eq_f
  imports Main
begin

definition logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_logic_eq x y \<longleftrightarrow> x = y"

theorem logic_eq_f:
  fixes f :: "'a \<Rightarrow> 'b"
    and x y :: "'a"
  assumes "logipedia_logic_eq x y"
  shows "logipedia_logic_eq (f x) (f y)"
  sorry

end
