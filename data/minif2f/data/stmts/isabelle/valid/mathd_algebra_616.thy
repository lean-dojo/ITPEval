(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_616 imports
Complex_Main

begin

theorem mathd_algebra_616:
  fixes f g :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = x^3 + 2 * x + 1"
    and h1 : "\<And>x. g x = x - 1"
  shows "f (g 1) = 1"
  by sorry

end