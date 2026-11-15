(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_123 imports
Complex_Main

begin

theorem mathd_algebra_123:
  fixes a b :: nat
  assumes h0 : "a + b = 20"
    and h1 : "a = 3 * b"
  shows "a - b = 10"
  by sorry

end