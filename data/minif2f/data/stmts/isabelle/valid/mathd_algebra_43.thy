(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_43 imports
  Complex_Main
begin

theorem mathd_algebra_43:
  fixes a b :: real
    and f :: "real \<Rightarrow> real"
  assumes h0 : "\<And>x. f x = a * x + b"
    and h1 : "f 7 = 4"
    and h2 : "f 6 = 3"
  shows "f 3 = 0"
  by sorry


end