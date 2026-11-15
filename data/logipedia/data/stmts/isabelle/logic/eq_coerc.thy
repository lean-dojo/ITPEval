(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_coerc,
  catalog title "logic.eq_coerc": equality of propositions transports truth
  from the first proposition to the second. This file contains no proof.
*)

theory eq_coerc
  imports Main
begin

definition logipedia_logic_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_logic_eq x y \<longleftrightarrow> x = y"

theorem logic_eq_coerc:
  "\<forall>A B :: bool.
    A \<longrightarrow>
    logipedia_logic_eq A B \<longrightarrow>
    B"
  sorry

end
