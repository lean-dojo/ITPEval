(*
  Statement-only formalization of VERINA corpus artifact verina_basic_63
  (verina__isabelle__verina_basic_63), catalog title "has_close_elements":
  an exact binary64 pair scan decides whether two finite list elements have
  IEEE-754 absolute difference below a nonnegative threshold, together with
  its precondition, executable implementation, pairwise postcondition, and
  final correctness proposition. This file contains no proof.
*)

theory verina_basic_63
  imports Complex_Main
begin

type_synonym binary64 = nat

definition b64_bits :: "binary64 \<Rightarrow> nat" where
  "b64_bits x = x mod 2 ^ 64"

definition b64_sign :: "binary64 \<Rightarrow> bool" where
  "b64_sign x \<longleftrightarrow> b64_bits x \<ge> 2 ^ 63"

definition b64_exponent :: "binary64 \<Rightarrow> nat" where
  "b64_exponent x = (b64_bits x div 2 ^ 52) mod 2 ^ 11"

definition b64_fraction :: "binary64 \<Rightarrow> nat" where
  "b64_fraction x = b64_bits x mod 2 ^ 52"

definition b64_is_nan :: "binary64 \<Rightarrow> bool" where
  "b64_is_nan x \<longleftrightarrow>
    b64_exponent x = 2 ^ 11 - 1 \<and> b64_fraction x \<noteq> 0"

definition b64_is_inf :: "binary64 \<Rightarrow> bool" where
  "b64_is_inf x \<longleftrightarrow>
    b64_exponent x = 2 ^ 11 - 1 \<and> b64_fraction x = 0"

definition b64_is_finite :: "binary64 \<Rightarrow> bool" where
  "b64_is_finite x \<longleftrightarrow>
    b64_exponent x < 2 ^ 11 - 1"

definition b64_pos_zero :: binary64 where
  "b64_pos_zero = 0"

definition b64_neg_zero :: binary64 where
  "b64_neg_zero = 2 ^ 63"

definition b64_pos_inf :: binary64 where
  "b64_pos_inf = (2 ^ 11 - 1) * 2 ^ 52"

definition b64_neg_inf :: binary64 where
  "b64_neg_inf = 2 ^ 63 + (2 ^ 11 - 1) * 2 ^ 52"

definition b64_canonical_nan :: binary64 where
  "b64_canonical_nan =
    (2 ^ 11 - 1) * 2 ^ 52 + 2 ^ 51"

definition b64_value :: "binary64 \<Rightarrow> real" where
  "b64_value x =
    (let s = (if b64_sign x then (-1 :: real) else 1);
         e = b64_exponent x;
         f = b64_fraction x
     in if e = 0
        then s * real f * (2 :: real) powi (-1074)
        else s * real (2 ^ 52 + f) * (2 :: real) powi (int e - 1075))"

definition b64_even_significand :: "binary64 \<Rightarrow> bool" where
  "b64_even_significand x \<longleftrightarrow> b64_fraction x mod 2 = 0"

definition b64_overflow_cutoff :: real where
  "b64_overflow_cutoff =
    (2 :: real) powi 1024 - (2 :: real) powi 970"

definition b64_round_candidate :: "real \<Rightarrow> binary64 \<Rightarrow> bool" where
  "b64_round_candidate r w \<longleftrightarrow>
    w < 2 ^ 64 \<and>
    b64_is_finite w \<and>
    \<not> b64_sign w \<and>
    (\<forall>v.
      v < 2 ^ 64 \<and> b64_is_finite v \<and> \<not> b64_sign v \<longrightarrow>
      abs (b64_value w - r) \<le> abs (b64_value v - r)) \<and>
    (\<forall>v.
      v < 2 ^ 64 \<and>
      b64_is_finite v \<and>
      \<not> b64_sign v \<and>
      abs (b64_value v - r) = abs (b64_value w - r) \<and>
      b64_even_significand v
      \<longrightarrow> b64_even_significand w)"

definition b64_round_nonnegative :: "real \<Rightarrow> binary64" where
  "b64_round_nonnegative r =
    (if r = 0 then b64_pos_zero
     else if r \<ge> b64_overflow_cutoff then b64_pos_inf
     else (THE w. b64_round_candidate r w))"

definition b64_negate :: "binary64 \<Rightarrow> binary64" where
  "b64_negate x = (b64_bits x + 2 ^ 63) mod 2 ^ 64"

definition b64_round :: "real \<Rightarrow> binary64" where
  "b64_round r =
    (if r < 0
     then b64_negate (b64_round_nonnegative (-r))
     else b64_round_nonnegative r)"

definition b64_subtract ::
    "binary64 \<Rightarrow> binary64 \<Rightarrow> binary64" where
  "b64_subtract a b =
    (if b64_is_nan a \<or> b64_is_nan b then b64_canonical_nan
     else if b64_is_inf a then
       (if b64_is_inf b \<and> b64_sign a = b64_sign b
        then b64_canonical_nan
        else if b64_sign a then b64_neg_inf else b64_pos_inf)
     else if b64_is_inf b then b64_negate b
     else if b64_value a = b64_value b then
       (if b64_bits a = b64_neg_zero \<and> b64_bits b = b64_pos_zero
        then b64_neg_zero
        else b64_pos_zero)
     else b64_round (b64_value a - b64_value b))"

definition b64_le :: "binary64 \<Rightarrow> binary64 \<Rightarrow> bool" where
  "b64_le a b \<longleftrightarrow>
    (if b64_is_nan a \<or> b64_is_nan b then False
     else if b64_bits a = b64_neg_inf then True
     else if b64_bits b = b64_pos_inf then True
     else if b64_bits a = b64_pos_inf
       then b64_bits b = b64_pos_inf
     else if b64_bits b = b64_neg_inf
       then b64_bits a = b64_neg_inf
     else b64_value a \<le> b64_value b)"

definition b64_lt :: "binary64 \<Rightarrow> binary64 \<Rightarrow> bool" where
  "b64_lt a b \<longleftrightarrow>
    (if b64_is_nan a \<or> b64_is_nan b then False
     else if b64_bits a = b64_neg_inf
       then b64_bits b \<noteq> b64_neg_inf
     else if b64_bits b = b64_pos_inf
       then b64_bits a \<noteq> b64_pos_inf
     else if b64_bits a = b64_pos_inf \<or>
             b64_bits b = b64_neg_inf
       then False
     else b64_value a < b64_value b)"

definition absDiff :: "binary64 \<Rightarrow> binary64 \<Rightarrow> binary64" where
  "absDiff a b =
    (let a_minus_b = b64_subtract a b
     in if b64_lt a_minus_b b64_pos_zero
        then b64_subtract b a
        else a_minus_b)"

definition has_close_elements_precond ::
    "binary64 list \<Rightarrow> binary64 \<Rightarrow> bool" where
  "has_close_elements_precond numbers threshold \<longleftrightarrow>
    b64_le b64_pos_zero threshold \<and>
    \<not> b64_is_nan threshold \<and>
    list_all b64_is_finite numbers"

fun has_close_elements_inner ::
    "binary64 list \<Rightarrow> binary64 \<Rightarrow> binary64 \<Rightarrow> bool" where
  "has_close_elements_inner [] current threshold = False"
| "has_close_elements_inner (earlier # rest) current threshold =
    (if b64_lt (absDiff earlier current) threshold
     then True
     else has_close_elements_inner rest current threshold)"

fun has_close_elements_outer ::
    "binary64 list \<Rightarrow> binary64 list \<Rightarrow> binary64 \<Rightarrow> bool"
    where
  "has_close_elements_outer prefix [] threshold = False"
| "has_close_elements_outer prefix (current # rest) threshold =
    (if has_close_elements_inner prefix current threshold
     then True
     else has_close_elements_outer (prefix @ [current]) rest threshold)"

definition has_close_elements ::
    "binary64 list \<Rightarrow> binary64 \<Rightarrow> bool" where
  "has_close_elements numbers threshold =
    has_close_elements_outer [] numbers threshold"

fun has_close_elements_pairwise_far ::
    "binary64 list \<Rightarrow> binary64 \<Rightarrow> bool" where
  "has_close_elements_pairwise_far [] threshold = True"
| "has_close_elements_pairwise_far (a # rest) threshold =
    (list_all (\<lambda>b. b64_le threshold (absDiff a b)) rest \<and>
     has_close_elements_pairwise_far rest threshold)"

definition has_close_elements_postcond ::
    "binary64 list \<Rightarrow> binary64 \<Rightarrow> bool \<Rightarrow> bool" where
  "has_close_elements_postcond numbers threshold result \<longleftrightarrow>
    ((\<not> result) \<longleftrightarrow>
      has_close_elements_pairwise_far numbers threshold)"

theorem has_close_elements_spec_satisfied:
  assumes "has_close_elements_precond numbers threshold"
  shows
    "has_close_elements_postcond
      numbers threshold (has_close_elements numbers threshold)"
  sorry

end
