(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_11 imports
  Complex_Main
begin

theorem mathd_algebra_11:
  fixes a b :: real
  assumes h0 : "a \<noteq> b"
    and h1 : "a \<noteq> 2 * b"
    and h2 : "(4*a+3*b) / (a-2*b) = 5"
  shows "(a+11*b) / (a-b) = 2"
  by sorry

end