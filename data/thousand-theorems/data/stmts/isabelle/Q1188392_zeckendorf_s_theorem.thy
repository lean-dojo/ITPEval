(*
  Statement-only formalization of thousand-theorems corpus artifact Q1188392,
  "Zeckendorf's theorem": the Fibonacci-sum map is a bijection from lists of
  nonconsecutive indices at least two to the natural numbers. This file
  contains no proof.
*)

theory Q1188392_zeckendorf_s_theorem
  imports Main
begin

fun q1188392_fib :: "nat \<Rightarrow> nat" where
  "q1188392_fib 0 = 0"
| "q1188392_fib (Suc 0) = 1"
| "q1188392_fib (Suc (Suc n)) =
    q1188392_fib (Suc n) + q1188392_fib n"

definition q1188392_is_zeckendorf_rep :: "nat list \<Rightarrow> bool" where
  "q1188392_is_zeckendorf_rep l \<longleftrightarrow>
    successively (\<lambda>a b. b + 2 \<le> a) (l @ [0])"

theorem zeckendorf_theorem:
  "bij_betw
    (\<lambda>l :: nat list. sum_list (map q1188392_fib l))
    {l. q1188392_is_zeckendorf_rep l}
    (UNIV :: nat set)"
  sorry

end
