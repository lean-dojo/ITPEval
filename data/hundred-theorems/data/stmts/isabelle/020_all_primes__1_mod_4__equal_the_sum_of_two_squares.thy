(*
  Statement-only formalization of "All Primes (1 mod 4) Equal the Sum of Two Squares" from
  Hundred Theorems item 020. This file contains no proof.
*)

theory All_Primes_1_Mod_4_Equal_Sum_Two_Squares
  imports Complex_Main
begin

theorem prime_one_mod_four_sum_of_two_squares:
  fixes p :: nat
  assumes "prime p"
    and "p mod 4 = 1"
  shows "\<exists>x y :: nat. p = x ^ 2 + y ^ 2"
  sorry

end
