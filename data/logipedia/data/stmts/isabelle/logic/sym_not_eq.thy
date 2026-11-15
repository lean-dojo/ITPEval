(*
  Statement-only formalization of Logipedia corpus artifact logic.sym_not_eq,
  catalog title "logic.sym_not_eq": symmetry of disequality for arbitrary
  elements of an arbitrary type. This file contains no proof.
*)

theory sym_not_eq
  imports Main
begin

definition logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_logic_eq x y \<longleftrightarrow> x = y"

definition logipedia_connectives_Not :: "bool \<Rightarrow> bool"
  where "logipedia_connectives_Not P \<longleftrightarrow> \<not> P"

theorem logic_sym_not_eq:
  "\<forall>x :: 'a.
    \<forall>y :: 'a.
      logipedia_connectives_Not (logipedia_logic_eq x y) \<longrightarrow>
      logipedia_connectives_Not (logipedia_logic_eq y x)"
  sorry

end
