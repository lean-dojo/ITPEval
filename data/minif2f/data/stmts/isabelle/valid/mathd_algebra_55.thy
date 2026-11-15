(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_55 imports
  Complex_Main
begin

theorem mathd_algebra_55:
  fixes q p :: real
  assumes h0 : "q = 2 - 4 + 6 - 8 + 10 -12 + 14"
    and h1 : "p = 3 - 6 + 9 - 12 + 15 - 18 + 21"
  shows "q/p = 2/3"
  by sorry

end