(*
  Authors: Wenda Li
*)

theory imo_1981_p6 
  imports Complex_Main "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem imo_1981_p6:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    and g :: "nat \<Rightarrow> nat"
  assumes "\<forall> y. f 0 y = y + 1"
    and "\<forall> x. f (x + 1) 0 = f x 1"
    and "\<forall> x y. f (x + 1) (y + 1) = f x (f (x + 1) y)"
    and "g 0 = 2"
    and "\<forall> n. g (n + 1) = 2^(g n)"
  shows "f 4 1981 = g 1983 - 3"
  by sorry

end
