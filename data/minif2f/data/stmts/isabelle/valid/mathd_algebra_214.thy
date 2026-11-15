(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_214 imports
  Complex_Main
begin

theorem mathd_algebra_214:
  fixes a :: real
    and f :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = a * (x-2)^2 + 3"
    and h1 : "f 4 = 4"
  shows "f 6 = 7"
  by sorry

end