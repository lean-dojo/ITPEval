(*
  Statement-only formalization of Logipedia corpus artifact bigops.mk_Aop:
  the formation principle for the abstract Aop predicate from a two-sided
  identity and associativity. This file contains no proof.
*)

theory mk_Aop
  imports Main
begin

consts Aop :: "'a \<Rightarrow> bool"

theorem mk_Aop:
  fixes nil :: 'a
    and op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes left_identity: "\<forall>a. op nil a = a"
    and right_identity: "\<forall>a. op a nil = a"
    and associative: "\<forall>a b c. op a (op b c) = op (op a b) c"
  shows "Aop nil"
  sorry

end
