(*
  Authors: Wenda Li
*)
theory amc12b_2002_p6 
  imports Complex_Main
begin

theorem amc12b_2002_p6:
  fixes a b :: real
  assumes "a \<noteq> 0 \<and> b \<noteq> 0"
      and "\<forall> x. x^2 + a * x + b = (x - a) * (x - b)"
    shows " a = 1 \<and> b = -2"
  by sorry
end 