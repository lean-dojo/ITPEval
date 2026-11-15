(*
  Statement-only formalization of thousand-theorems corpus artifact Q16251580
  (thousand-theorems__isabelle__Q16251580), "Matiyasevich's theorem":
  membership in a recursively defined Pell sequence is equivalent to a system
  of natural-number Diophantine and congruence conditions. This file contains
  no proof.
*)

theory Q16251580_matiyasevich_s_theorem
  imports Main
begin

fun q16251580_pell :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "q16251580_pell a 0 = (1, 0)"
| "q16251580_pell a (Suc n) =
    (fst (q16251580_pell a n) * a +
       (a * a - 1) * snd (q16251580_pell a n),
     fst (q16251580_pell a n) +
       snd (q16251580_pell a n) * a)"

definition q16251580_xn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q16251580_xn a n = fst (q16251580_pell a n)"

definition q16251580_yn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q16251580_yn a n = snd (q16251580_pell a n)"

definition q16251580_congruent ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "q16251580_congruent m n modulus \<longleftrightarrow>
    m mod modulus = n mod modulus"

theorem matiyasevic:
  fixes a k x y :: nat
  shows
    "(1 < a \<and> q16251580_xn a k = x \<and> q16251580_yn a k = y)
      \<longleftrightarrow>
     1 < a \<and> k \<le> y \<and>
       ((x = 1 \<and> y = 0) \<or>
        (\<exists>u v s t b :: nat.
          x * x - (a * a - 1) * y * y = 1 \<and>
          u * u - (a * a - 1) * v * v = 1 \<and>
          s * s - (b * b - 1) * t * t = 1 \<and>
          1 < b \<and>
          q16251580_congruent b 1 (4 * y) \<and>
          q16251580_congruent b a u \<and>
          0 < v \<and>
          y * y dvd v \<and>
          q16251580_congruent s x u \<and>
          q16251580_congruent t k (4 * y)))"
  sorry

end
