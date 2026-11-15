(*
  Statement-only formalization of Logipedia corpus artifact
  bool.eq_match_bool_type_false, catalog title
  bool.eq_match_bool_type_false: the polymorphic Boolean matcher applied to
  false is Leibniz-equal to its false branch for every result type and pair
  of branch values. This file contains no proof.
*)

theory eq_match_bool_type_false
  imports Main
begin

typedecl logipedia_bool

consts
  logipedia_false :: logipedia_bool
  logipedia_match_bool_type ::
    "'a \<Rightarrow> 'a \<Rightarrow> logipedia_bool \<Rightarrow> 'a"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_leibniz x y \<equiv>
      (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

theorem eq_match_bool_type_false:
  "\<forall>case_true :: 'a. \<forall>case_false :: 'a.
    logipedia_leibniz
      (logipedia_match_bool_type case_true case_false logipedia_false)
      case_false"
  sorry

end
