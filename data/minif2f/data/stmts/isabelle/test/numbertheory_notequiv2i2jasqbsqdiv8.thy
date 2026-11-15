(*
  Authors: Wenda Li
*)

theory numbertheory_notequiv2i2jasqbsqdiv8 imports 
  Complex_Main 
  "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem numbertheory_notequiv2i2jasqbsqdiv8:
  shows "\<not> (\<forall> a b :: int.
    ((\<exists> i j. a = 2*i \<and> b=2*j)
      \<longleftrightarrow> (\<exists> k. a^2 + b^2 = 8*k)))"
  by sorry

end
