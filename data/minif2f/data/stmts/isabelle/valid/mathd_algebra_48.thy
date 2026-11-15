(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_48 imports
  Complex_Main
begin

theorem mathd_algebra_48:
  fixes q e :: complex
  assumes h0 : "q = 9 - 4 * \<i>"
    and h1 : "e = -3 - 4 * \<i>"
  shows "q - e = 12"
  by sorry

end
