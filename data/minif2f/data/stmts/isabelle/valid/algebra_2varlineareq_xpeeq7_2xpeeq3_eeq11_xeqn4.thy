(*
  Authors: Albert Qiaochu Jiang
*)

theory algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4 imports
Complex_Main

begin

theorem algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4:
  fixes x e :: complex
  assumes h0 : "x + e = 7"
    and h1 : "2 * x + e = 3"
  shows "e=11 \<and> x= (-4)"
  by sorry


end