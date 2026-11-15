(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527230 (thousand-theorems__hol4__Q3527230), "Von Staudt–Clausen theorem":
  at every even natural index n, the Bernoulli number B_n plus the reciprocal
  sum over primes p < n + 2 with p - 1 dividing n is an integer. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory dividesTheory integerTheory;
open pred_setTheory primeTheory ratTheory;

val q3527230_is_bernoulli_def = new_definition (
  "q3527230_is_bernoulli_def",
  ``q3527230_is_bernoulli (b : num -> rat) <=>
      !n : num.
        ITSET
          (\j : num. \acc : rat.
             rat_of_num (binomial n j) * b j + acc)
          (count n)
          0q =
        if n = 1 then 1q else 0q``);

val q3527230_bernoulli_def = new_definition (
  "q3527230_bernoulli_def",
  ``q3527230_bernoulli =
      (@b : num -> rat. q3527230_is_bernoulli b)``);

val q3527230_prime_correction_def = new_definition (
  "q3527230_prime_correction_def",
  ``q3527230_prime_correction (n : num) =
      ITSET
        (\p : num. \acc : rat. 1q / rat_of_num p + acc)
        {p : num |
          p < n + 2 /\
          prime p /\
          divides (p - 1) n}
        0q``);

val q3527230_is_integer_def = new_definition (
  "q3527230_is_integer_def",
  ``q3527230_is_integer (q : rat) <=>
      ?z : int. q = rat_of_int z``);

val von_staudt_clausen_theorem =
  ``!n : num.
      EVEN n ==>
      q3527230_is_integer
        (q3527230_bernoulli n +
         q3527230_prime_correction n)``;
