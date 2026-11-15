(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_433 imports
  Complex_Main
begin

theorem mathd_algebra_433:
  fixes f :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = 3 * sqrt (2 * x -7) - 8"
  shows "f 8 = 1"
  by sorry


end