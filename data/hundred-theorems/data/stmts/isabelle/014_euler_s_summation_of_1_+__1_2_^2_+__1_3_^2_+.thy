section \<open>Bernoulli numbers and the zeta function at positive integers\<close>
theory Bernoulli_Zeta
imports 
  "HOL-Complex_Analysis.Complex_Analysis"
  Bernoulli_FPS
begin

(* TODO: Move *)
lemma joinpaths_cong: "f = f' \<Longrightarrow> g = g' \<Longrightarrow> f +++ g = f' +++ g'"
  by sorry

lemma linepath_cong: "a = a' \<Longrightarrow> b = b' \<Longrightarrow> linepath a b = linepath a' b'"
  by sorry

text \<open>
  The analytic continuation of the exponential generating function of the Bernoulli numbers
  is $\frac{z}{e^z - 1}$, which has simple poles at all $2ki\pi$ for $k\in\mathbb{Z}\setminus\{0\}$.
  We will need the residue at these poles:
\<close>
lemma residue_bernoulli:
  assumes "n \<noteq> 0"
  shows   "residue (\<lambda>z. 1 / (z ^ m * (exp z - 1))) (2 * pi * real_of_int n * \<i>) = 
             1 / (2 * pi * real_of_int n * \<i>) ^ m"
  by sorry

text \<open>
  At positive integers greater than 1, the Riemann zeta function is simply the infinite
  sum $\zeta(n) = \sum_{k=1}^\infty k^{-n}$. For even $n$, this quantity can also be
  expressed in terms of Bernoulli numbers.

  To show this, we employ a similar strategy as in the meromorphic asymptotics approach:
  We apply the Residue Theorem to the exponential generating function of the Bernoulli numbers:
  \[\sum_{n=0}^\infty \frac{B_n}{n!} z^n = \frac{z}{e^z - 1}\]
  Recall that this function has poles at $2ki\pi$ for $k\in\mathbb{Z}\setminus\{0\}$.
  In the meromorphic asymptotics case, we integrated along a circle of radius $3i\pi$ in order
  to get the dominant singularities $2i\pi$ and $-2i\pi$. Now, however, we will not use a 
  fixed integration path, but we let the integration path become bigger and bigger. 
  Because the integrand decays relatively quickly if $n > 1$, the integral vanishes in the limit 
  and we obtain not just an asymptotic formula, but an exact representation of $B_n$ as an 
  infinite sum.

  For odd $n$, we have $B_n = 0$, but for even $n$, the residues at $2ki\pi$ and $-2ki\pi$ 
  combine nicely to $2\cdot(-2k\pi)^{-n}$, and after some simplification we get the formula
  for $B_n$.

  Another difference to the meromorphic asymptotics is that we now use a rectangle instead
  of a circle as the integration path. For the asymptotics, only a big-oh bound was needed
  for the integral over one fixed integration path, and the circular path was very convenient.
  However, now we need to explicitly bound the integral for a whole sequence of integration paths
  that grow in size, and bounding $e^z - 1$ for $z$ on a circle is very tedious. On a rectangle,
  this term can be bounded much more easily. Still, we have to do this separately for all four
  edges of the rectangle, which will be a bit tedious.
\<close>
theorem nat_even_power_sums_complex:
  assumes n': "n' > 0"
  shows   "(\<lambda>k. 1 / of_nat (Suc k) ^ (2*n') :: complex) sums
             of_real ((-1) ^ Suc n' * bernoulli (2*n') * (2 * pi) ^ (2 * n') / (2 * fact (2*n')))"
  by sorry

corollary nat_even_power_sums_real:
  assumes n': "n' > 0"
  shows   "(\<lambda>k. 1 / real (Suc k) ^ (2*n')) sums
             ((-1) ^ Suc n' * bernoulli (2*n') * (2 * pi) ^ (2 * n') / (2 * fact (2*n')))"
    (is "?f sums ?L")
  by sorry

lemma sgn_of_int: "sgn (of_int n) = (of_int (sgn n) :: 'a :: linordered_idom)"
  by sorry

text \<open>
  We can now also easily determine the signs of Bernoulli numbers: the above formula 
  clearly shows that the signs of $B_{2n}$ alternate as $n$ increases, and we already know
  that $B_{2n+1} = 0$ for any positive $n$. A lot of other facts about the signs of
  Bernoulli numbers follow.
\<close>
corollary sgn_bernoulli_num_even:
  assumes "n > 0"
  shows   "sgn (bernoulli_num (2 * n)) = (-1) ^ Suc n"
  by sorry

lemma sgn_bernoulli_even:
  assumes "n > 0"
  shows   "sgn (bernoulli (2 * n)) = ((-1) ^ Suc n :: 'a :: linordered_field)"
  by sorry

corollary bernoulli_even_nonzero:
  assumes "even n"
  shows   "bernoulli n \<noteq> (0 :: 'a :: field_char_0)"
  by sorry

corollary sgn_bernoulli: 
  "sgn (bernoulli n :: 'a :: linordered_field) = 
     (if n = 0 then 1 else if n = 1 then -1 else if odd n then 0 else (-1) ^ Suc (n div 2))"
  by sorry

corollary bernoulli_zero_iff: "bernoulli n = 0 \<longleftrightarrow> odd n \<and> n \<noteq> 1"
  by sorry

corollary bernoulli'_zero_iff: "(bernoulli' n = 0) \<longleftrightarrow> (n \<noteq> 1 \<and> odd n)"
  by sorry

lemma bernoulli_num_eq_0_iff: "bernoulli_num n = 0 \<longleftrightarrow> odd n \<and> n \<noteq> 1"
  by sorry

corollary bernoulli_pos_iff: "bernoulli n > (0 :: 'a :: linordered_field) \<longleftrightarrow> n = 0 \<or> n mod 4 = 2"
  by sorry

corollary bernoulli_neg_iff: "(bernoulli n :: 'a :: linordered_field) < 0 \<longleftrightarrow> n = 1 \<or> n > 0 \<and> 4 dvd n"
  by sorry


text \<open>
  We also get the solution of the Basel problem (the sum over all squares of positive
  integers) and any `Basel-like' problem with even exponent. The case of odd exponents
  is much more complicated and no similarly nice closed form is known for these.
\<close>

corollary nat_squares_sums: "(\<lambda>n. 1 / (n+1) ^ 2) sums (pi ^ 2 / 6)"
  by sorry

corollary nat_power4_sums: "(\<lambda>n. 1 / (n+1) ^ 4) sums (pi ^ 4 / 90)"
  by sorry

corollary nat_power6_sums: "(\<lambda>n. 1 / (n+1) ^ 6) sums (pi ^ 6 / 945)"
  by sorry

corollary nat_power8_sums: "(\<lambda>n. 1 / (n+1) ^ 8) sums (pi ^ 8 / 9450)"
  by sorry

end
