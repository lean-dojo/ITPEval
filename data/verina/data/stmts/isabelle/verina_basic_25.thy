(*
  Statement-only formalization of VERINA corpus artifact verina_basic_25
  (verina__isabelle__verina_basic_25), catalog title "sumAndAverage": an
  executable range-sum program returns the integer sum and its IEEE-754
  binary64 average, together with the input bound, postcondition, and final
  correctness proposition. Float values are represented by their 64-bit
  encodings, preserving NaNs, infinities, signed zeros, and Lean Float BEq.
  This file contains no proof.
*)

theory verina_basic_25
  imports Main "HOL.Real"
begin

typedef lean_float = "{bits::nat. bits < 2 ^ 64}"
  by (rule exI[of _ 0], simp)

definition float64_of_bits :: "nat \<Rightarrow> lean_float" where
  "float64_of_bits bits = Abs_lean_float (bits mod (2 ^ 64))"

definition binary64_fraction :: "lean_float \<Rightarrow> nat" where
  "binary64_fraction bits =
    Rep_lean_float bits mod (2 ^ 52)"

definition binary64_exponent :: "lean_float \<Rightarrow> nat" where
  "binary64_exponent bits =
    (Rep_lean_float bits div (2 ^ 52)) mod 2048"

definition binary64_finite_nonnegative :: "lean_float \<Rightarrow> bool" where
  "binary64_finite_nonnegative bits \<longleftrightarrow>
    Rep_lean_float bits < 2 ^ 63 \<and>
    binary64_exponent bits < 2047"

definition binary64_value :: "lean_float \<Rightarrow> real" where
  "binary64_value bits =
    (let exponent = binary64_exponent bits;
         fraction = binary64_fraction bits
     in
       if exponent = 0 then
         real fraction / real (2 ^ 1074)
       else if exponent \<le> 1075 then
         real (2 ^ 52 + fraction) /
           real (2 ^ (1075 - exponent))
       else
         real (2 ^ 52 + fraction) *
           real (2 ^ (exponent - 1075)))"

definition binary64_even :: "lean_float \<Rightarrow> bool" where
  "binary64_even bits \<longleftrightarrow>
    even (Rep_lean_float bits)"

definition binary64_rounds :: "real \<Rightarrow> lean_float \<Rightarrow> bool" where
  "binary64_rounds value rounded \<longleftrightarrow>
    binary64_finite_nonnegative rounded \<and>
    (\<forall>candidate.
      binary64_finite_nonnegative candidate \<longrightarrow>
        abs (value - binary64_value rounded) \<le>
          abs (value - binary64_value candidate)) \<and>
    (\<forall>candidate.
      binary64_finite_nonnegative candidate \<and>
      candidate \<noteq> rounded \<and>
      abs (value - binary64_value rounded) =
        abs (value - binary64_value candidate) \<and>
      binary64_even candidate
      \<longrightarrow> binary64_even rounded)"

definition binary64_round :: "real \<Rightarrow> lean_float" where
  "binary64_round value =
    (THE rounded. binary64_rounds value rounded)"

definition lean_nat_log2 :: "nat \<Rightarrow> nat" where
  "lean_nat_log2 n =
    (THE result.
      if n < 2 then
        result = 0
      else
        2 ^ result \<le> n \<and> n < 2 ^ (result + 1))"

definition lean_float_scaleB ::
    "lean_float \<Rightarrow> nat \<Rightarrow> lean_float" where
  "lean_float_scaleB bits shift =
    binary64_round
      (binary64_value bits * real (2 ^ shift))"

definition lean_float_of_nat :: "nat \<Rightarrow> lean_float" where
  "lean_float_of_nat n =
    (let shift = lean_nat_log2 n - 63;
         mantissa = n div (2 ^ shift)
     in
       lean_float_scaleB
         (binary64_round (real mantissa))
         shift)"

definition lean_float_div ::
    "lean_float \<Rightarrow> lean_float \<Rightarrow> lean_float" where
  "lean_float_div numerator denominator =
    binary64_round
      (binary64_value numerator / binary64_value denominator)"

definition binary64_is_nan :: "lean_float \<Rightarrow> bool" where
  "binary64_is_nan bits \<longleftrightarrow>
    binary64_exponent bits = 2047 \<and>
    binary64_fraction bits \<noteq> 0"

definition binary64_is_zero :: "lean_float \<Rightarrow> bool" where
  "binary64_is_zero bits \<longleftrightarrow>
    binary64_exponent bits = 0 \<and>
    binary64_fraction bits = 0"

definition lean_float_beq ::
    "lean_float \<Rightarrow> lean_float \<Rightarrow> bool" where
  "lean_float_beq left right \<longleftrightarrow>
    \<not> binary64_is_nan left \<and>
    \<not> binary64_is_nan right \<and>
    (left = right \<or>
      (binary64_is_zero left \<and> binary64_is_zero right))"

definition result_beq ::
    "(int \<times> lean_float) \<Rightarrow> (int \<times> lean_float) \<Rightarrow> bool" where
  "result_beq left right \<longleftrightarrow>
    fst left = fst right \<and>
    lean_float_beq (snd left) (snd right)"

definition float64_positive_zero :: lean_float where
  "float64_positive_zero = float64_of_bits 0"

definition sumAndAverage_precond :: "nat \<Rightarrow> bool" where
  "sumAndAverage_precond n \<longleftrightarrow>
    0 < n \<and> n < 9007199254740992"

definition range_sum_to :: "nat \<Rightarrow> nat" where
  "range_sum_to n = sum_list [0..<Suc n]"

definition sumAndAverage :: "nat \<Rightarrow> int \<times> lean_float" where
  "sumAndAverage n =
    (if n \<le> 0
     then (0, float64_positive_zero)
     else
       (int (range_sum_to n),
        lean_float_div
          (lean_float_of_nat (range_sum_to n))
          (lean_float_of_nat n)))"

definition sumAndAverage_postcond ::
    "nat \<Rightarrow> (int \<times> lean_float) \<Rightarrow> bool" where
  "sumAndAverage_postcond n result \<longleftrightarrow>
    (n = 0 \<longrightarrow>
      result_beq result (0, float64_positive_zero)) \<and>
    (0 < n \<longrightarrow>
      fst result = int (n * (n + 1) div 2) \<and>
      lean_float_beq
        (snd result)
        (lean_float_div
          (lean_float_of_nat (n * (n + 1) div 2))
          (lean_float_of_nat n)))"

theorem sumAndAverage_spec_satisfied:
  assumes "sumAndAverage_precond n"
  shows "sumAndAverage_postcond n (sumAndAverage n)"
  sorry

end
