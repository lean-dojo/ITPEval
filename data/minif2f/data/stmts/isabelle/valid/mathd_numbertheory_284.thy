(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_numbertheory_284 imports
  Complex_Main
begin

theorem mathd_numbertheory_284:
  fixes a b :: nat
  assumes h0 : "1\<le>a \<and> a \<le>9 \<and> b \<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"
  by sorry

end