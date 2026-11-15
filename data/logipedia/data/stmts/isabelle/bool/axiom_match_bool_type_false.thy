(*
  Statement-only formalization of Logipedia corpus artifact
  bool.axiom_match_bool_type_false, catalog title
  bool.axiom_match_bool_type_false: the polymorphic Boolean matcher applied to
  false is related by the source equality predicate to its false branch for
  every result type and pair of branch values. This file contains no proof.
*)

theory axiom_match_bool_type_false
  imports Main
begin

typedecl logipedia_bool

consts
  logipedia_false :: logipedia_bool
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  logipedia_match_bool_type ::
    "'a \<Rightarrow> 'a \<Rightarrow> logipedia_bool \<Rightarrow> 'a"

theorem axiom_match_bool_type_false:
  "\<forall>case_true :: 'a. \<forall>case_false :: 'a.
    logipedia_connectives_equal
      (logipedia_match_bool_type case_true case_false logipedia_false)
      case_false"
  sorry

end
