(*
  Authors: Wenda Li
*)

theory amc12b_2002_p3 imports
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
begin

theorem amc12b_2002_p3:
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"
  by sorry

end
