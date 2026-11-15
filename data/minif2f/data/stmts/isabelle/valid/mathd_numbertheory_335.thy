(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_numbertheory_335 imports
  Complex_Main
begin

theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
  by sorry


end