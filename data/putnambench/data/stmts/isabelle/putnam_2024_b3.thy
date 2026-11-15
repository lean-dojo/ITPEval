(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b3
  (putnambench__isabelle__putnam_2024_b3): consecutive positive solutions
  r_n of tan x = x are separated by more than pi and by less than pi plus
  1 / ((n^2 + n) * pi). This file contains no proof.
*)

theory putnam_2024_b3
  imports Complex_Main
begin

theorem putnam_2024_b3:
  fixes r :: "nat \<Rightarrow> real"
    and n :: nat
  assumes hr_mono: "strict_mono_on {1..} r"
    and hr_first: "\<forall>x\<in>{0<..<r 1}. tan x \<noteq> x"
    and hr_roots:
      "\<forall>m :: nat.
        0 < m \<longrightarrow>
          0 < r m \<and>
          tan (r m) = r m \<and>
          (\<forall>x\<in>{r m<..<r (m + 1)}. tan x \<noteq> x)"
    and hn: "0 < n"
  shows
    "r (n + 1) - r n - pi
      \<in> {0<..<1 / ((real n ^ 2 + real n) * pi)}"
  sorry

end
