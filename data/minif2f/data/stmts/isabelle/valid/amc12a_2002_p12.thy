(*
  Authors: Wenda Li
*)

theory amc12a_2002_p12 imports
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem amc12a_2002_p12:
  fixes f :: "real => real"
    and k :: real
    and a b :: nat
  assumes "\<forall> x. f x = x^2 - 63 * x + k"
    and "f (of_nat a) = 0 \<and> f (of_nat b) = 0"
    and "a \<noteq> b"
    and "prime a \<and> prime b"
  shows "k=122"
  by sorry

end
