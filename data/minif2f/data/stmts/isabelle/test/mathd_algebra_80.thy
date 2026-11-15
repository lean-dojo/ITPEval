(*
  Authors: Wenda Li
*)
theory mathd_algebra_80 imports Complex_Main
begin

theorem mathd_algebra_80:
  fixes x :: real
  assumes "x \<noteq> -1"
      and "(x - 9) / (x + 1) = 2"
    shows "x = -11"
  by sorry

end