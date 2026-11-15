(*
  Statement-only formalization of "The Irrationality of the Square Root of 2"
  from Hundred Theorems item 001. The Diophantine statement is equivalent to
  saying that no rational number has square 2. This file contains no proof.
*)

theory Irrationality_Of_Square_Root_Of_2
  imports Main
begin

theorem sqrt_two_irrational:
  "\<nexists>p q :: nat. q \<noteq> 0 \<and> p * p = 2 * (q * q)"
  sorry

end
