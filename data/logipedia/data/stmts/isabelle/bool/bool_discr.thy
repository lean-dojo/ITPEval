(*
  Statement-only formalization of Logipedia corpus artifact bool.bool_discr,
  catalog title bool.bool_discr: equal Boolean values select the reflexive
  proposition rather than the contradictory branch in the nested Boolean
  discriminator. This file contains no proof.
*)

theory bool_discr
  imports Main
begin

definition match_bool_type :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a"
  where "match_bool_type case_true case_false b \<equiv>
    (if b then case_true else case_false)"

theorem bool_discr:
  "\<forall>x::bool. \<forall>y::bool. x = y \<longrightarrow>
    match_bool_type
      (match_bool_type
        (\<forall>P::bool. P \<longrightarrow> P)
        (\<forall>P::bool. P)
        y)
      (match_bool_type
        (\<forall>P::bool. P)
        (\<forall>P::bool. P \<longrightarrow> P)
        y)
      x"
  sorry

end
