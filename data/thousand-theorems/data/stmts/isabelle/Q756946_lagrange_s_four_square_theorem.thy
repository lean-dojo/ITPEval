(*
  Statement-only formalization of the thousand-theorems corpus artifact Q756946
  (thousand-theorems__isabelle__Q756946), "Lagrange's four-square theorem":
  every natural number is the sum of the squares of four natural numbers.
  This file contains no proof.
*)

theory Q756946_lagrange_s_four_square_theorem
  imports Main
begin

theorem sum_four_squares:
  fixes n :: nat
  shows "\<exists>a b c d :: nat. a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n"
  sorry

end
