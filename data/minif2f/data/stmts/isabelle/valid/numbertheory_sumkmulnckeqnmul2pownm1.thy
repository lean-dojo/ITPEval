(*
  Authors: Albert Qiaochu Jiang
*)

theory numbertheory_sumkmulnckeqnmul2pownm1 imports
  Complex_Main
  "HOL-Number_Theory.Number_Theory"

begin

theorem numbertheory_sumkmulnckeqnmul2pownm1:
  fixes n :: nat
  assumes h0 : "0 < n"
  shows "(\<Sum> k = 1..n. k * (n choose k)) = n * 2^(n-1)"
  by sorry

end
