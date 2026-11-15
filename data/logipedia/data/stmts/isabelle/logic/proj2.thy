(*
  Statement-only formalization of Logipedia corpus artifact logic.proj2,
  catalog title "logic.proj2": second projection from a conjunction of two
  arbitrary propositions. This file contains no proof.
*)

theory proj2
  imports Main
begin

theorem logic_proj2:
  "\<forall>A B :: bool.
    (A \<and> B) \<longrightarrow> B"
  sorry

end
