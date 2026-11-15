(*
  Statement-only formalization of thousand-theorems corpus artifact Q282649,
  "Pentagonal number theorem": over an arbitrary possibly trivial unital
  commutative ring, the coefficientwise infinite product of the formal power
  series 1 - X^(n+1) is the series supported on the generalized pentagonal
  numbers, with coefficients alternating according to the integer index.
  This file contains no proof.
*)

theory Q282649_pentagonal_number_theorem
  imports Complex_Main
begin

type_synonym 'a q282649_fps = "nat \<Rightarrow> 'a"

definition q282649_fps_one ::
    "'a::comm_ring \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_one u n = (if n = 0 then u else 0)"

definition q282649_fps_X ::
    "'a::comm_ring \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_X u n = (if n = 1 then u else 0)"

definition q282649_fps_sub ::
    "'a::comm_ring q282649_fps \<Rightarrow>
      'a q282649_fps \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_sub f g n = f n - g n"

definition q282649_fps_mul ::
    "'a::comm_ring q282649_fps \<Rightarrow>
      'a q282649_fps \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_mul f g n = (\<Sum>i\<le>n. f i * g (n - i))"

fun q282649_fps_pow ::
    "'a::comm_ring \<Rightarrow>
      'a q282649_fps \<Rightarrow> nat \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_pow u f 0 = q282649_fps_one u"
  | "q282649_fps_pow u f (Suc n) =
      q282649_fps_mul f (q282649_fps_pow u f n)"

fun q282649_fps_list_prod ::
    "'a::comm_ring \<Rightarrow>
      (nat \<Rightarrow> 'a q282649_fps) \<Rightarrow>
      nat list \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_list_prod u f [] = q282649_fps_one u"
  | "q282649_fps_list_prod u f (i # is) =
      q282649_fps_mul (f i) (q282649_fps_list_prod u f is)"

definition q282649_fps_finite_prod ::
    "'a::comm_ring \<Rightarrow>
      (nat \<Rightarrow> 'a q282649_fps) \<Rightarrow>
      nat set \<Rightarrow> 'a q282649_fps"
  where
    "q282649_fps_finite_prod u f s =
      q282649_fps_list_prod u f (sorted_list_of_set s)"

definition q282649_pentagonal :: "int \<Rightarrow> nat" where
  "q282649_pentagonal k = nat (k * (3 * k - 1) div 2)"

definition q282649_neg_one_pow ::
    "'a::comm_ring \<Rightarrow> int \<Rightarrow> 'a"
  where
    "q282649_neg_one_pow u k = (if even k then u else -u)"

definition q282649_pentagonal_series ::
    "'a::comm_ring \<Rightarrow> 'a q282649_fps"
  where
  "q282649_pentagonal_series u =
    (\<lambda>n.
      if \<exists>k::int. q282649_pentagonal k = n
      then q282649_neg_one_pow u (SOME k. q282649_pentagonal k = n)
      else 0)"

definition q282649_has_prod ::
    "'a::{comm_ring,topological_space} \<Rightarrow>
      (nat \<Rightarrow> 'a q282649_fps) \<Rightarrow>
      'a q282649_fps \<Rightarrow> bool"
  where
    "q282649_has_prod u f p \<longleftrightarrow>
      (\<forall>k. ((\<lambda>s. q282649_fps_finite_prod u f s k) \<longlongrightarrow> p k)
        (finite_subsets_at_top UNIV))"

theorem pentagonal_number_theorem:
  fixes u :: "'a::{comm_ring,topological_space}"
  assumes unit: "\<And>x. u * x = x"
  shows "q282649_has_prod u
    (\<lambda>n. q282649_fps_sub
      (q282649_fps_one u)
      (q282649_fps_pow u (q282649_fps_X u) (n + 1)))
    (q282649_pentagonal_series u)"
  oops

end
