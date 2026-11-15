(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_le_minus_minus_comm, catalog title
  "nat.minus_le_minus_minus_comm": for natural numbers a, b, and c with
  c at most b, subtracting b minus c from a equals subtracting b from a plus
  c, using truncated natural-number subtraction. This file contains no proof.
*)

theory minus_le_minus_minus_comm
  imports Main
begin

theorem logipedia_nat_minus_le_minus_minus_comm:
  "\<forall>b c a :: nat.
    c \<le> b \<longrightarrow> a - (b - c) = (a + c) - b"
  sorry

end
