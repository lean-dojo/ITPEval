(*
  Statement-only formalization of Logipedia corpus artifact logic.trans_eq,
  catalog title "logic.trans_eq": transitivity of polymorphic equality over
  an arbitrary type. This file contains no proof.
*)

theory trans_eq
  imports Main
begin

definition logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_logic_eq x y \<longleftrightarrow> x = y"

theorem logic_trans_eq:
  "\<forall>x y z :: 'a.
    logipedia_logic_eq x y \<longrightarrow>
    logipedia_logic_eq y z \<longrightarrow>
    logipedia_logic_eq x z"
  sorry

end
