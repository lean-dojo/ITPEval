(*
  Authors: Wenda Li
*)

theory aime_1983_p1 imports Complex_Main
begin

theorem aime_1983_p1:
  fixes x y z w :: nat
  assumes ht : "1 < x \<and> 1 < y \<and> 1 < z"
    and hw : "0 \<le> w"
    and h0 : "ln w / ln x = 24"
    and h1 : "ln w / ln y = 40"
    and h2 : "ln w / ln (x * y * z) = 12"
  shows "ln w / ln z = 60"
  by sorry

end
