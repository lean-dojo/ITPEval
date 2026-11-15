(*
  Authors: Wenda Li
*)

theory mathd_numbertheory_764 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

definition inv_mod::"nat \<Rightarrow> nat \<Rightarrow> nat" where
  "inv_mod d p = (SOME x. x < p \<and> (x * d) mod p = 1)"

theorem mathd_numbertheory_764:
  fixes p :: nat
  assumes "prime p"
  and "7 \<le> p" 
shows "(\<Sum> k \<in> {1..<p-1}. (inv_mod k p) * (inv_mod (k+1) p))
  mod p = 2"
  by sorry

end
