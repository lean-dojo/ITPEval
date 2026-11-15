(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_247 imports
Complex_Main

begin

theorem mathd_algebra_247:
  fixes t s :: real
    and n :: nat
  assumes h0 : "t = 2 * s - s^2"
    and h1 : "s = n^2 - 2^n + 1"
    and h2 : "n=3"
  shows "t=0"
  by sorry


end