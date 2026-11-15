(*
  Statement-only formalization of Logipedia corpus artifact
  bool.eq_match_bool_type_true, catalog title
  bool.eq_match_bool_type_true: the polymorphic Boolean matcher applied to
  true is Leibniz-equal to its true branch for every result type and pair
  of branch values. This file contains no proof.
*)

theory eq_match_bool_type_true
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

theorem eq_match_bool_type_true:
  "\<forall>case_true :: 'a. \<forall>case_false :: 'a.
    logipedia_leibniz
      (logipedia_match_bool_type case_true case_false logipedia_true)
      case_true"
  sorry

end
