(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b5
  (putnambench__isabelle__putnam_2024_b5): counting pairs of nondecreasing
  positive integer sequences with a common bounded upper endpoint, and
  expressing that count by a rational polynomial with nonnegative
  coefficients. This file contains no proof.
*)

theory putnam_2024_b5
  imports Complex_Main
begin

definition putnam_2024_b5_qualifying :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "putnam_2024_b5_qualifying w z \<longleftrightarrow>
    w \<noteq> [] \<and>
    sorted w \<and>
    1 \<le> hd w \<and>
    last w \<le> z"

definition putnam_2024_b5_coeff :: "rat list \<Rightarrow> nat \<Rightarrow> rat" where
  "putnam_2024_b5_coeff a i =
    (if i < length a then a ! i else 0)"

definition putnam_2024_b5_poly_eval :: "rat list \<Rightarrow> rat \<Rightarrow> rat" where
  "putnam_2024_b5_poly_eval a t =
    (\<Sum>i < length a. putnam_2024_b5_coeff a i * t ^ i)"

theorem putnam_2024_b5:
  fixes k m :: nat
    and f :: "nat \<Rightarrow> nat"
  assumes hk: "0 < k"
    and hm: "0 < m"
    and f_def:
      "\<forall>n :: nat.
        f n =
          card
            {(x :: nat list, y :: nat list, z :: nat).
              length x = k \<and>
              putnam_2024_b5_qualifying x z \<and>
              length y = m \<and>
              putnam_2024_b5_qualifying y z \<and>
              z \<le> n}"
  shows
    "\<exists>a :: rat list.
      (\<forall>n :: nat.
        n > 0 \<longrightarrow>
          rat_of_nat (f n) =
            putnam_2024_b5_poly_eval a (rat_of_nat n)) \<and>
      (\<forall>i :: nat. 0 \<le> putnam_2024_b5_coeff a i)"
  sorry

end
