(*
  Authors: Wenda Li
*)

theory numbertheory_3pow2pownm1mod2pownp3eq2pownp2 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Number_Theory.Number_Theory"
begin

theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2:
  fixes n :: nat
  assumes "0 < n" 
  shows "(3^(2^n) - 1) mod (2^(n + 3)) = (2::nat)^(n + 2)"
  by sorry

end   