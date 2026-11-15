(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a1
  (putnambench__isabelle__putnam_2025_a1): positive integer sequences related
  by a rational recurrence have only finitely many indices at which the
  transformed terms are not relatively prime. This file contains no proof.
*)

theory putnam_2025_a1
  imports Complex_Main
begin

theorem putnam_2025_a1:
  fixes m n :: "nat \<Rightarrow> nat"
  assumes hm: "\<forall>k :: nat. 0 < m k"
    and hn: "\<forall>k :: nat. 0 < n k"
    and h_distinct: "m 0 \<noteq> n 0"
    and h_coprime:
      "\<forall>k :: nat. 0 < k \<longrightarrow> coprime (m k) (n k)"
    and h_recurrence:
      "\<forall>k :: nat.
        rat_of_nat (m (k + 1)) / rat_of_nat (n (k + 1)) =
          (2 * rat_of_nat (m k) + 1) /
            (2 * rat_of_nat (n k) + 1)"
  shows
    "finite
      {k :: nat.
        \<not> coprime (2 * m k + 1) (2 * n k + 1)}"
  sorry

end
