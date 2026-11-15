(*
  Statement-only formalization of Logipedia corpus artifact nat.injective_S,
  catalog title nat.injective_S: the successor function on natural numbers is
  injective. This file contains no proof.
*)

theory injective_S
  imports Main
begin

theorem injective_S:
  "\<forall>x y :: nat. Suc x = Suc y \<longrightarrow> x = y"
  sorry

end
