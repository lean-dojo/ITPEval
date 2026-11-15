(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_f2,
  catalog title "logic.eq_f2": applying a curried binary function preserves
  equality in both arguments across arbitrary source and target types. This
  file contains no proof.
*)

theory eq_f2
  imports Main
begin

definition logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_logic_eq x y \<longleftrightarrow> x = y"

theorem logic_eq_f2:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
    and x1 x2 :: "'a"
    and y1 y2 :: "'b"
  assumes "logipedia_logic_eq x1 x2"
    and "logipedia_logic_eq y1 y2"
  shows "logipedia_logic_eq (f x1 y1) (f x2 y2)"
  sorry

end
