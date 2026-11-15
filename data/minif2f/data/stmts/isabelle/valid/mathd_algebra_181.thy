(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_181 imports
Complex_Main

begin

theorem mathd_algebra_181:
  fixes n :: real
  assumes h0 : "n \<noteq> 3"
    and h1 : "(n+5) / (n-3) = 2"
  shows "n=11"
  by sorry


end