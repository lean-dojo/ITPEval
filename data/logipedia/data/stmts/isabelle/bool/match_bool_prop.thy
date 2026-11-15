(*
  Statement-only formalization of Logipedia corpus artifact
  bool.match_bool_prop, catalog title bool.match_bool_prop: any predicate
  holding for the designated true and false values holds for every value of
  the abstract Boolean carrier. This file contains no proof.
*)

theory match_bool_prop
  imports Main
begin

typedecl logipedia_bool

consts
  logipedia_true :: logipedia_bool
  logipedia_false :: logipedia_bool

theorem match_bool_prop:
  "\<forall>P :: logipedia_bool \<Rightarrow> bool.
    P logipedia_true \<longrightarrow>
    P logipedia_false \<longrightarrow>
    (\<forall>z :: logipedia_bool. P z)"
  sorry

end
