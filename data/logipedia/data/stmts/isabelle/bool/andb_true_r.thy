(*
  Statement-only formalization of Logipedia corpus artifact bool.andb_true_r,
  catalog title bool.andb_true_r: Boolean conjunction being true implies that
  its right operand is true. This file contains no proof.
*)

theory andb_true_r
  imports Main
begin

definition andb :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "andb b1 b2 \<equiv> (if b1 then b2 else False)"

theorem andb_true_r:
  "\<forall>b1::bool. \<forall>b2::bool. andb b1 b2 = True \<longrightarrow> b2 = True"
  sorry

end
