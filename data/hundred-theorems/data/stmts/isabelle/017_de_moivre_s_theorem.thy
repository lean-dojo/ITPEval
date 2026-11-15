(*
  Statement-only formalization of De Moivre's theorem from Hundred Theorems
  item 017, using Isabelle/HOL's complex cis function. This file contains no
  proof.
*)

theory De_Moivre_Theorem
  imports Complex_Main
begin

theorem de_moivre:
  fixes x :: real
    and n :: nat
  shows "cis x ^ n = cis (real n * x)"
  sorry

end
