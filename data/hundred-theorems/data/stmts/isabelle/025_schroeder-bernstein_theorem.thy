(*
  Statement-only formalization of the Schroeder-Bernstein theorem from
  Hundred Theorems item 025. Injections in both directions imply a bijection.
  This file contains no proof.
*)

theory Schroeder_Bernstein_Theorem
  imports Main
begin

theorem schroeder_bernstein:
  fixes f :: "'a \<Rightarrow> 'b"
    and g :: "'b \<Rightarrow> 'a"
  assumes "inj f"
    and "inj g"
  shows "\<exists>h :: 'a \<Rightarrow> 'b. bij h"
  sorry

end
