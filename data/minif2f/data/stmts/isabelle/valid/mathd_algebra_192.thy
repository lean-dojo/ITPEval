(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_192 imports
  Complex_Main
begin

theorem mathd_algebra_192:
  fixes q e d :: complex
  assumes h0 : "q = 11 - 5 * \<i>"
    and h1 : "e = 11 + 5 * \<i>"
    and h2 : "d = 2 * \<i>"
  shows "q * e * d = 292 * \<i>"
  by sorry

end
