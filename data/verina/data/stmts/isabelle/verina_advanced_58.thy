(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_58,
  catalog title "nthUglyNumber": an executable three-index dynamic program
  returns the nth positive natural number whose prime factors are only 2, 3,
  and 5, with its counting-based correctness contract. This file contains no
  proof.
*)

theory verina_advanced_58
  imports Main
begin

definition nthUglyNumber_precond :: "nat \<Rightarrow> bool" where
  "nthUglyNumber_precond n \<longleftrightarrow> n > 0"

fun uglyListGet :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "uglyListGet [] i = 0"
| "uglyListGet (x # xs) 0 = x"
| "uglyListGet (x # xs) (Suc i) = uglyListGet xs i"

definition nextUgly ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> nat \<times> nat \<times> nat \<times> nat" where
  "nextUgly seq c2 c3 c5 =
    (let i2 = uglyListGet seq c2 * 2;
         i3 = uglyListGet seq c3 * 3;
         i5 = uglyListGet seq c5 * 5;
         next = min i2 (min i3 i5);
         c2' = (if next = i2 then c2 + 1 else c2);
         c3' = (if next = i3 then c3 + 1 else c3);
         c5' = (if next = i5 then c5 + 1 else c5)
     in (next, c2', c3', c5'))"

fun nthUglyNumber_loop ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> nat list" where
  "nthUglyNumber_loop 0 seq c2 c3 c5 = seq"
| "nthUglyNumber_loop (Suc i) seq c2 c3 c5 =
    (case nextUgly seq c2 c3 c5 of
       (next, c2', c3', c5') \<Rightarrow>
         nthUglyNumber_loop i (seq @ [next]) c2' c3' c5')"

definition nthUglyNumber :: "nat \<Rightarrow> nat" where
  "nthUglyNumber n =
    uglyListGet
      (nthUglyNumber_loop (n - 1) [1] 0 0 0)
      (n - 1)"

fun divideOutFuel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "divideOutFuel 0 n p = n"
| "divideOutFuel (Suc fuel) n p =
    (if p > 1 \<and> n > 0 \<and> n mod p = 0
     then divideOutFuel fuel (n div p) p
     else n)"

definition divideOut :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "divideOut n p = divideOutFuel n n p"

definition isUgly :: "nat \<Rightarrow> bool" where
  "isUgly x =
    (if x = 0
     then False
     else
       (let n1 = divideOut x 2;
            n2 = divideOut n1 3;
            n3 = divideOut n2 5
        in n3 = 1))"

definition nthUglyNumber_postcond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nthUglyNumber_postcond n result \<longleftrightarrow>
    isUgly result \<and>
    length (filter isUgly [0..<result]) = n - 1"

theorem nthUglyNumber_spec_satisfied:
  assumes "nthUglyNumber_precond n"
  shows "nthUglyNumber_postcond n (nthUglyNumber n)"
  sorry

end
