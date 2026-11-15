(*
  Statement-only formalization of Logipedia corpus artifact bigops.mk_ACop:
  the formation principle for the abstract ACop predicate from a two-sided
  identity, associativity, and commutativity. This file contains no proof.
*)

theory mk_ACop
  imports Main
begin

consts ACop :: "'a \<Rightarrow> bool"

theorem mk_ACop:
  fixes nil :: 'a
    and op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes left_identity: "\<forall>a. op nil a = a"
    and right_identity: "\<forall>a. op a nil = a"
    and associative: "\<forall>a b c. op a (op b c) = op (op a b) c"
    and commutative: "\<forall>a b. op a b = op b a"
  shows "ACop nil"
  sorry

end
