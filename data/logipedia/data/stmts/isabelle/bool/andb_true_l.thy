(*
  Statement-only formalization of Logipedia corpus artifact bool.andb_true_l,
  catalog title bool.andb_true_l: Boolean conjunction being true implies that
  its left operand is true. This file contains no proof.
*)

theory andb_true_l
  imports Main
begin

definition andb :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "andb b1 b2 \<equiv> (if b1 then b2 else False)"

theorem andb_true_l:
  "\<forall>b1::bool. \<forall>b2::bool. andb b1 b2 = True \<longrightarrow> b1 = True"
  sorry

end
