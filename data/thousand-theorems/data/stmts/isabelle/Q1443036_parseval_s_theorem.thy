(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1443036 (thousand-theorems__isabelle__Q1443036), "Parseval's theorem":
  for a complex-valued square-integrable function on a circle of positive
  period, the sum over all integer Fourier modes of the squared coefficient
  norms equals its normalized squared L2 norm. This file contains no proof.
*)

theory Q1443036_parseval_s_theorem
  imports Complex_Main
begin

definition q1443036_real_riemann_sum ::
    "nat \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "q1443036_real_riemann_sum n T g =
    (if n = 0 then 0
     else (\<Sum>k<n. (T / real n) * g (T * real k / real n)))"

definition q1443036_complex_riemann_sum ::
    "nat \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex" where
  "q1443036_complex_riemann_sum n T g =
    (if n = 0 then 0
     else (\<Sum>k<n. of_real (T / real n) * g (T * real k / real n)))"

definition q1443036_real_integral ::
    "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "q1443036_real_integral T g =
    Lim at_top (\<lambda>n. q1443036_real_riemann_sum (Suc n) T g)"

definition q1443036_complex_integral ::
    "real \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex" where
  "q1443036_complex_integral T g =
    Lim at_top (\<lambda>n. q1443036_complex_riemann_sum (Suc n) T g)"

definition q1443036_l2_distance_squared ::
    "real \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow>
      (real \<Rightarrow> complex) \<Rightarrow> real" where
  "q1443036_l2_distance_squared T g h =
    (1 / T) *
      q1443036_real_integral T (\<lambda>x. norm (g x - h x) ^ 2)"

definition q1443036_l2_representative ::
    "real \<Rightarrow> (nat \<Rightarrow> real \<Rightarrow> complex) \<Rightarrow> bool" where
  "q1443036_l2_representative T f \<longleftrightarrow>
    (\<forall>m. continuous_on {0..T} (f m)) \<and>
    (\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
      q1443036_l2_distance_squared T (f m) (f n) < e)"

definition q1443036_fourier_coefficient ::
    "real \<Rightarrow> (nat \<Rightarrow> real \<Rightarrow> complex) \<Rightarrow>
      int \<Rightarrow> complex" where
  "q1443036_fourier_coefficient T f n =
    Lim at_top
      (\<lambda>m.
        of_real (1 / T) *
          q1443036_complex_integral T
            (\<lambda>x.
              exp (- (\<i> * of_real (2 * pi * real_of_int n * x / T))) *
                f m x))"

definition q1443036_l2_norm_squared ::
    "real \<Rightarrow> (nat \<Rightarrow> real \<Rightarrow> complex) \<Rightarrow> real" where
  "q1443036_l2_norm_squared T f =
    Lim at_top
      (\<lambda>m.
        (1 / T) *
          q1443036_real_integral T (\<lambda>x. norm (f m x) ^ 2))"

theorem q1443036_parseval_s_theorem:
  fixes T :: real
    and f :: "nat \<Rightarrow> real \<Rightarrow> complex"
  assumes period_positive: "0 < T"
    and l2_function: "q1443036_l2_representative T f"
  shows
    "suminf
        (\<lambda>n::int. norm (q1443036_fourier_coefficient T f n) ^ 2) =
      q1443036_l2_norm_squared T f"
  sorry

end
