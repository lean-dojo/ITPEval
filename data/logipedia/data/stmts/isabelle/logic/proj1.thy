(*
  Statement-only formalization of Logipedia corpus artifact logic.proj1,
  catalog title "logic.proj1": first projection from a conjunction of two
  arbitrary propositions. This file contains no proof.
*)

theory proj1
  imports Main
begin

theorem logic_proj1:
  "\<forall>A B :: bool.
    (A \<and> B) \<longrightarrow> A"
  sorry

end
