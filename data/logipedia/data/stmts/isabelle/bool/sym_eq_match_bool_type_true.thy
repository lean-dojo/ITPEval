(*
  Statement-only formalization of Logipedia corpus artifact
  bool.sym_eq_match_bool_type_true, catalog title
  bool.sym_eq_match_bool_type_true: for every result type and pair of branch
  values, the true branch is Leibniz-equal to the polymorphic Boolean matcher
  applied to the abstract true value. This file contains no proof.
*)

theory sym_eq_match_bool_type_true
  imports Main
begin

typedecl logipedia_bool

consts
  logipedia_true :: logipedia_bool
  logipedia_match_bool_type ::
    "'a \<Rightarrow> 'a \<Rightarrow> logipedia_bool \<Rightarrow> 'a"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_leibniz x y \<equiv>
      (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem sym_eq_match_bool_type_true:
  "\<forall>case_true :: 'a. \<forall>case_false :: 'a.
    logipedia_leibniz
      case_true
      (logipedia_match_bool_type case_true case_false logipedia_true)"
  sorry

end
