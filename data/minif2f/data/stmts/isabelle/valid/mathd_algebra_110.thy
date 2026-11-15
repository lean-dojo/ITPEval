(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_110 imports
  Complex_Main
begin

theorem mathd_algebra_110:
  fixes q e :: complex
  assumes h0 : "q = 2 - 2 * \<i>"
    and h1 : "e = 5 + 5 * \<i>"
  shows "q * e = 20"
  by sorry

end
