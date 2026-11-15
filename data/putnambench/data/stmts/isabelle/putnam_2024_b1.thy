(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b1
  (putnambench__isabelle__putnam_2024_b1): the positive grid sizes and integer
  offsets admitting a nonattacking selection whose entries are exactly 1
  through n are precisely (2*l+1, l+1). This file contains no proof.
*)

theory putnam_2024_b1
  imports Complex_Main
begin

definition putnam_2024_b1_valid :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "putnam_2024_b1_valid n k \<longleftrightarrow>
    0 < n \<and>
    0 < k \<and>
    (\<exists>f :: nat \<Rightarrow> nat.
      bij_betw f {0..<n} {0..<n} \<and>
      (\<lambda>i. int (Suc i) + int (Suc (f i)) - int k) ` {0..<n}
        = {1..int n})"

definition putnam_2024_b1_solution :: "(nat \<times> nat) set" where
  "putnam_2024_b1_solution =
    (\<lambda>l :: nat. (2 * l + 1, l + 1)) ` UNIV"

theorem putnam_2024_b1:
  shows
    "{(n, k). putnam_2024_b1_valid n k} =
      putnam_2024_b1_solution"
  sorry

end
