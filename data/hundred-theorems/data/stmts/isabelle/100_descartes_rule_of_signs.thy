(*
  File:    Descartes_Sign_Rule.thy
  Author:  Manuel Eberl <manuel@pruvisto.org>

  Descartes' Rule of Signs, which relates the number of positive real roots of a polynomial
  with the number of sign changes in its coefficient list.
*)
section \<open>Sign changes and Descartes' Rule of Signs\<close>

theory Descartes_Sign_Rule
imports 
  Complex_Main
  "HOL-Computational_Algebra.Polynomial"
begin

lemma op_plus_0: "((+) (0 :: 'a :: monoid_add)) = id"
  by sorry

lemma filter_dropWhile: 
  "filter (\<lambda>x. \<not>P x) (dropWhile P xs) = filter (\<lambda>x. \<not>P x) xs"
  by sorry


subsection \<open>Polynomials\<close> 

text\<open>
  A real polynomial whose leading and constant coefficients have opposite
  non-zero signs must have a positive root.
\<close>
lemma pos_root_exI:
  assumes "poly p 0 * lead_coeff p < (0 :: real)"
  obtains x where "x > 0" "poly p x = 0"
  by sorry

text \<open>
  Substitute $X$ with $aX$ in a polynomial $p(X)$. This turns all the $X - a$ factors in $p$
  into factors of the form $X - 1$.
\<close>
definition reduce_root where
  "reduce_root a p = pcompose p [:0, a:]"

lemma reduce_root_pCons: 
  "reduce_root a (pCons c p) = pCons c (smult a (reduce_root a p))"
  by sorry

lemma reduce_root_nonzero [simp]: 
  "a \<noteq> 0 \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> reduce_root a p \<noteq> (0 :: 'a :: idom poly)"
  by sorry


subsection \<open>List of partial sums\<close>

text \<open>
  We first define, for a given list, the list of accumulated partial sums from left to right: 
  the list @{term "psums xs"} has as its $i$-th entry $\sum_{j=0}^i \mathrm{xs}_i$.
\<close>

fun psums where
  "psums [] = []"
| "psums [x] = [x]"
| "psums (x#y#xs) = x # psums ((x+y) # xs)"

lemma length_psums [simp]: "length (psums xs) = length xs"
  by sorry

lemma psums_Cons: 
  "psums (x#xs) = (x :: 'a :: semigroup_add) # map ((+) x) (psums xs)"
  by sorry

lemma last_psums: 
  "(xs :: 'a :: monoid_add list) \<noteq> [] \<Longrightarrow> last (psums xs) = sum_list xs"
  by sorry

lemma psums_0_Cons [simp]: 
  "psums (0#xs :: 'a :: monoid_add list) = 0 # psums xs"
  by sorry

lemma map_uminus_psums: 
  fixes xs :: "'a :: ab_group_add list"
  shows "map uminus (psums xs) = psums (map uminus xs)"
  by sorry

lemma psums_replicate_0_append:
  "psums (replicate n (0 :: 'a :: monoid_add) @ xs) = 
     replicate n 0 @ psums xs"
  by sorry

lemma psums_nth: "n < length xs \<Longrightarrow> psums xs ! n = (\<Sum>i\<le>n. xs ! i)"
  by sorry


subsection \<open>Sign changes in a list\<close>

text \<open>
  Next, we define the number of sign changes in a sequence. Intuitively, this is the number 
  of times that, when passing through the list, a sign change between one element and the next 
  element occurs (while ignoring all zero entries).

  We implement this by filtering all zeros from the list of signs, removing all adjacent equal 
  elements and taking the length of the resulting list minus one.
\<close>
definition sign_changes :: "('a :: {sgn,zero} list) \<Rightarrow> nat" where
  "sign_changes xs = length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))) - 1"

lemma sign_changes_Nil [simp]: "sign_changes [] = 0" 
  by sorry

lemma sign_changes_singleton [simp]: "sign_changes [x] = 0" 
  by sorry

lemma sign_changes_cong:
  assumes "map sgn xs = map sgn ys"
  shows   "sign_changes xs = sign_changes ys"
  by sorry

lemma sign_changes_Cons_ge: "sign_changes (x # xs) \<ge> sign_changes xs"
  by sorry

lemma sign_changes_Cons_Cons_different: 
  fixes x y :: "'a :: linordered_idom"
  assumes "x * y < 0"
  shows "sign_changes (x # y # xs) = 1 + sign_changes (y # xs)"
  by sorry

lemma sign_changes_Cons_Cons_same: 
  fixes x y :: "'a :: linordered_idom"
  shows "x * y > 0 \<Longrightarrow> sign_changes (x # y # xs) = sign_changes (y # xs)"
  by sorry

lemma sign_changes_0_Cons [simp]: 
  "sign_changes (0 # xs :: 'a :: idom_abs_sgn list) = sign_changes xs"
  by sorry

lemma sign_changes_two: 
  fixes x y :: "'a :: linordered_idom"
  shows "sign_changes [x,y] = 
           (if x > 0 \<and> y < 0 \<or> x < 0 \<and> y > 0 then 1 else 0)"
  by sorry

lemma sign_changes_induct [case_names nil sing zero nonzero]:
  assumes "P []" "\<And>x. P [x]" "\<And>xs. P xs \<Longrightarrow> P (0#xs)"
          "\<And>x y xs. x \<noteq> 0 \<Longrightarrow> P ((x + y) # xs) \<Longrightarrow> P (x # y # xs)"
  shows   "P xs"
  by sorry

lemma sign_changes_filter: 
  fixes xs :: "'a :: linordered_idom list"
  shows "sign_changes (filter (\<lambda>x. x \<noteq> 0) xs) = sign_changes xs"
  by sorry

lemma sign_changes_Cons_Cons_0: 
  fixes xs :: "'a :: linordered_idom list"
  shows "sign_changes (x # 0 # xs) = sign_changes (x # xs)"
  by sorry

lemma sign_changes_uminus: 
  fixes xs :: "'a :: linordered_idom list"
  shows   "sign_changes (map uminus xs) = sign_changes xs"
  by sorry

lemma sign_changes_replicate: "sign_changes (replicate n x) = 0"
  by sorry

lemma sign_changes_decompose:
  assumes "x \<noteq> (0 :: 'a :: linordered_idom)"
  shows   "sign_changes (xs @ x # ys) = 
             sign_changes (xs @ [x]) + sign_changes (x # ys)"
  by sorry

text \<open>
  If the first and the last entry of a list are non-zero, its number of sign changes is even 
  if and only if the first and the last element have the same sign. This will be important 
  later to establish the base case of Descartes' Rule. (if there are no positive roots, 
  the number of sign changes is even)
\<close>
lemma even_sign_changes_iff:
  assumes "xs \<noteq> ([] :: 'a :: linordered_idom list)" "hd xs \<noteq> 0" "last xs \<noteq> 0"
  shows   "even (sign_changes xs) \<longleftrightarrow> sgn (hd xs) = sgn (last xs)"
  by sorry


subsection \<open>Arthan's lemma\<close>

context
begin

text \<open>
  We first prove an auxiliary lemma that allows us to assume w.l.o.g. that the first element of 
  the list is non-negative, similarly to what Arthan does in his proof.
\<close>
private lemma arthan_wlog [consumes 3, case_names nonneg lift]:
  fixes xs :: "'a :: linordered_idom list"
  assumes "xs \<noteq> []" "last xs \<noteq> 0" "x + y + sum_list xs = 0"
  assumes "\<And>x y xs. xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0 \<Longrightarrow> 
               x + y + sum_list xs = 0 \<Longrightarrow> x \<ge> 0 \<Longrightarrow> P x y xs"
  assumes "\<And>x y xs. xs \<noteq> [] \<Longrightarrow> P x y xs \<Longrightarrow> P (-x) (-y) (map uminus xs)"
  shows   "P x y xs"
proof (cases "x \<ge> 0")
  assume x: "\<not>(x \<ge> 0)"
  from assms have "map uminus xs \<noteq> []" by simp
  moreover from x assms(1,2,3) have"P (-x) (-y) (map uminus xs)"
    using uminus_sum_list_map[of "\<lambda>x. x" xs, symmetric]
    by (intro assms) (auto simp: last_map algebra_simps o_def neg_eq_iff_add_eq_0)
  ultimately have "P (- (-x)) (- (-y)) (map uminus (map uminus xs))" by (rule assms)
  thus ?thesis by (simp add: o_def)
qed (simp_all add: assms)

text \<open>
  We now show that the $\alpha$ and $\beta$ in Arthan's proof have the necessary properties:
  their difference is non-negative and even.
\<close>
private lemma arthan_aux1:
  fixes xs :: "'a :: {linordered_idom} list"
  assumes "xs \<noteq> []" "last xs \<noteq> 0" "x + y + sum_list xs = 0"
  defines "v \<equiv> \<lambda>xs. int (sign_changes xs)"
  shows "v (x # y # xs) - v ((x + y) # xs) \<ge> 
             v (psums (x # y # xs)) - v (psums ((x + y) # xs)) \<and> 
         even (v (x # y # xs) - v ((x + y) # xs) - 
                  (v (psums (x # y # xs)) - v (psums ((x + y) # xs))))"
using assms(1-3)
proof (induction rule: arthan_wlog)
  have uminus_v: "v (map uminus xs) = v xs" for xs by (simp add: v_def sign_changes_uminus)

  case (lift x y xs)
  note lift(2)
  also have "v (psums (x#y#xs)) - v (psums ((x+y)#xs)) =
                 v (psums (- x # - y # map uminus xs)) - 
                 v (psums ((- x + - y) # map uminus xs))"
    by (subst (1 2) uminus_v [symmetric]) (simp add: map_uminus_psums)
  also have "v (x # y # xs) - v ((x + y) # xs) = 
                 v (-x # -y # map uminus xs) - v ((-x + -y) # map uminus xs)"
    by (subst (1 2) uminus_v [symmetric]) simp
  finally show ?case .
next
  case (nonneg x y xs)
  define p where "p = (LEAST n. xs ! n \<noteq> 0)"
  define xs1 :: "'a list" where "xs1 = replicate p 0"
  define xs2 where "xs2 = drop (Suc p) xs"
  from nonneg have "xs ! (length xs - 1) \<noteq> 0" by (simp add: last_conv_nth)
  hence p_nz: "xs ! p \<noteq> 0" unfolding p_def by (rule LeastI)
  {
    fix q assume "q < p" hence "xs ! q = 0"
      using Least_le[of "\<lambda>n. xs ! n \<noteq> 0" q] unfolding p_def by force
  } note less_p_zero = this
  from Least_le[of "\<lambda>n. xs ! n \<noteq> 0" "length xs - 1"] nonneg 
    have "p \<le> length xs - 1" unfolding p_def by (auto simp: last_conv_nth)
  with nonneg have p_less_length: "p < length xs" by (cases xs) simp_all

  from p_less_length less_p_zero have "take p xs = replicate p 0" 
    by (subst list_eq_iff_nth_eq) auto
  with p_less_length have xs_decompose: "xs = xs1 @ xs ! p # xs2" 
    unfolding xs1_def xs2_def
    by (subst append_take_drop_id [of p, symmetric], 
        subst Cons_nth_drop_Suc) simp_all

  have v_decompose: "v (xs' @ xs) = v (xs' @ [xs ! p]) + v (xs ! p # xs2)" for xs'
  proof -
    have "xs' @ xs = (xs' @ xs1) @ xs ! p # xs2" by (subst xs_decompose) simp
    also have "v \<dots> = v (xs' @ [xs ! p]) + v (xs ! p # xs2)" unfolding v_def
      by (subst sign_changes_decompose[OF p_nz], 
          subst (1 2 3 4) sign_changes_filter [symmetric]) (simp_all add: xs1_def)
    finally show ?thesis .
  qed

  have psums_decompose: "psums xs = replicate p 0 @ psums (xs!p # xs2)" 
    by (subst xs_decompose) (simp add: xs1_def psums_replicate_0_append)
  have v_psums_decompose: "sign_changes (xs' @ psums xs) = sign_changes (xs' @ [xs!p]) + 
         sign_changes (xs!p # map ((+) (xs!p)) (psums xs2))" for xs'
  proof -
    fix xs' :: "'a list"
    have "sign_changes (xs' @ psums xs) = 
            sign_changes (xs' @ xs ! p # map ((+) (xs!p)) (psums xs2))"
      by (subst psums_decompose, subst (1 2) sign_changes_filter [symmetric]) 
         (simp_all add: psums_Cons)
    also have "\<dots> = sign_changes (xs' @ [xs!p]) + 
                      sign_changes (xs!p # map ((+) (xs!p)) (psums xs2))"
      by (subst sign_changes_decompose[OF p_nz]) simp_all
    finally show "sign_changes (xs' @ psums xs) = \<dots>" .
  qed

  show ?case
  proof (cases "x > 0")
    assume "\<not>(x > 0)"
    with nonneg show ?thesis by (auto simp: v_def)
  next
    assume x: "x > 0"
    show ?thesis
    proof (rule linorder_cases[of y 0])
      assume y: "y > 0"
      from x and this have xy: "x + y > 0" by (rule add_pos_pos)
      with y have "sign_changes ((x + y) # xs) = sign_changes (y # xs)"
        by (intro sign_changes_cong) auto
      moreover have "sign_changes (x # psums ((x + y) # xs)) = 
                       sign_changes (psums ((x+y) # xs))"
        using x xy by (subst (1 2) psums_Cons) (simp_all add: sign_changes_Cons_Cons_same)
      ultimately show ?thesis using x y 
        by (simp add: v_def algebra_simps sign_changes_Cons_Cons_same)
    next
      assume y: "y = 0"
      with x show ?thesis
        by (simp add: v_def sign_changes_Cons_Cons_0 psums_Cons 
                      o_def sign_changes_Cons_Cons_same)
    next
      assume y: "y < 0"
      with x have different: "x * y < 0" by (rule mult_pos_neg)
      show ?thesis
      proof (rule linorder_cases[of "x + y" 0])
        assume xy: "x + y < 0"
        with x have different': "x * (x + y) < 0" by (rule mult_pos_neg)
        have "(\<lambda>t. t + (x + y)) = ((+) (x + y))" by (rule ext) simp
        moreover from y xy have "sign_changes ((x+y) # xs) = sign_changes (y # xs)" 
          by (intro sign_changes_cong) auto
        ultimately show ?thesis using xy different different' y
          by (simp add: v_def sign_changes_Cons_Cons_different psums_Cons o_def add_ac)
      next
        assume xy: "x + y = 0"
        show ?case
        proof (cases "xs ! p > 0")
          assume p: "xs ! p > 0"
          from p y have different': "y * xs ! p < 0" by (intro mult_neg_pos)
          with v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] x xy p different different' 
               v_psums_decompose[of "[x]"] v_psums_decompose[of "[]"]
          show ?thesis by (auto simp add: algebra_simps v_def sign_changes_Cons_Cons_0 
                             sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        next
          assume "\<not>(xs ! p > 0)"
          with p_nz have p: "xs ! p < 0" by simp
          from p y have same: "y * xs ! p > 0" by (intro mult_neg_neg)
          from p x have different': "x * xs ! p < 0" by (intro mult_pos_neg)
          from v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] xy different different' same 
               v_psums_decompose[of "[x]"] v_psums_decompose[of "[]"]
          show ?thesis by (auto simp add: algebra_simps v_def sign_changes_Cons_Cons_0 
                             sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        qed
      next
        assume xy: "x + y > 0"
        from x and this have same: "x * (x + y) > 0" by (rule mult_pos_pos)
        show ?case
        proof (cases "xs ! p > 0")
          assume p: "xs ! p > 0"
          from xy p have same': "(x + y) * xs ! p > 0" by (intro mult_pos_pos)
          from p y have different': "y * xs ! p < 0" by (intro mult_neg_pos)
          have "(\<lambda>t. t + (x + y)) = ((+) (x + y))" by (rule ext) simp
          with v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] different different' same same'
          show ?thesis by (auto simp add: algebra_simps v_def psums_Cons o_def
                             sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        next
          assume "\<not>(xs ! p > 0)"
          with p_nz have p: "xs ! p < 0" by simp
          from xy p have different': "(x + y) * xs ! p < 0" by (rule mult_pos_neg)
          from y p have same': "y * xs ! p > 0" by (rule mult_neg_neg)
          have "(\<lambda>t. t + (x + y)) = ((+) (x + y))" by (rule ext) simp
          with v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] different different' same same'
          show ?thesis by (auto simp add: algebra_simps v_def psums_Cons o_def
                              sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        qed
      qed
    qed
  qed
qed


text \<open>
  Now we can prove the main lemma of the proof by induction over the list with our specialised
  induction rule for @{term "sign_changes"}. It states that for a non-empty list whose last element 
  is non-zero and whose sum is zero, the difference of the sign changes in the list and in the list 
  of its partial sums is odd and positive. 
\<close>
lemma arthan:
  fixes xs :: "'a :: linordered_idom list"
  assumes "xs \<noteq> []" "last xs \<noteq> 0" "sum_list xs = 0"
  shows   "sign_changes xs > sign_changes (psums xs) \<and> 
           odd (sign_changes xs - sign_changes (psums xs))"
  by sorry

end


subsection \<open>Roots of a polynomial with a certain property\<close>

text \<open>
  The set of roots of a polynomial @{term "p"} that fulfil a given property @{term "P"}:
\<close>
definition "roots_with P p = {x. P x \<and> poly p x = 0}"

text \<open>
  The number of roots of a polynomial @{term "p"} with a given property @{term "P"}, where 
  multiple roots are counted multiple times.
 \<close>
definition "count_roots_with P p = (\<Sum>x\<in>roots_with P p. order x p)"

abbreviation "pos_roots \<equiv> roots_with (\<lambda>x. x > 0)"
abbreviation "count_pos_roots \<equiv> count_roots_with (\<lambda>x. x > 0)"


lemma finite_roots_with [simp]: 
  "(p :: 'a :: linordered_idom poly) \<noteq> 0 \<Longrightarrow> finite (roots_with P p)"
  by sorry

lemma count_roots_with_times_root:
  assumes "p \<noteq> 0" "P (a :: 'a :: linordered_idom)"
  shows   "count_roots_with P ([:a, -1:] * p) = Suc (count_roots_with P p)"
  by sorry


subsection \<open>Coefficient sign changes of a polynomial\<close>

abbreviation (input) "coeff_sign_changes f \<equiv> sign_changes (coeffs f)"

text \<open>
  We first show that when building a polynomial from a coefficient list, the coefficient sign
  sign changes of the resulting polynomial are the same as the same sign changes in the list.

  Note that constructing a polynomial from a list removes all trailing zeros.
\<close>
lemma sign_changes_coeff_sign_changes:
  assumes "Poly xs = (p :: 'a :: linordered_idom poly)"
  shows   "sign_changes xs = coeff_sign_changes p"
  by sorry

text \<open>
  By applying @{term "reduce_root a"}, we can assume w.l.o.g. that the root in
  question is 1, since applying root reduction does not change the number of 
  sign changes.
\<close>
lemma coeff_sign_changes_reduce_root: 
  assumes "a > (0 :: 'a :: linordered_idom)"
  shows   "coeff_sign_changes (reduce_root a p) = coeff_sign_changes p"
  by sorry

text \<open>
  Multiplying a polynomial with a positive constant also does not change the number 
  of sign changes. (in fact, any non-zero constant would also work, but the proof 
  is slightly more difficult and positive constants suffice in our use case)
\<close>
lemma coeff_sign_changes_smult: 
  assumes "a > (0 :: 'a :: linordered_idom)"
  shows   "coeff_sign_changes (smult a p) = coeff_sign_changes p"
  by sorry


context
begin

text \<open>
  We now show that a polynomial with an odd number of sign changes contains a 
  positive root. We first assume that the constant coefficient is non-zero. Then it is 
  clear that the polynomial's sign at 0 will be the sign of the constant coefficient, whereas 
  the polynomial's sign for sufficiently large inputs will be the sign of the leading coefficient.

  Moreover, we have shown before that in a list with an odd number of sign changes and 
  non-zero initial and last coefficients, the initial coefficient and the last coefficient have 
  opposite and non-zero signs. Then, the polynomial obviously has a positive root.
\<close>
private lemma odd_coeff_sign_changes_imp_pos_roots_aux:
  assumes [simp]: "p \<noteq> (0 :: real poly)" "poly p 0 \<noteq> 0"
  assumes "odd (coeff_sign_changes p)"
  obtains x where "x > 0" "poly p x = 0"
proof -
  from \<open>poly p 0 \<noteq> 0\<close>
  have [simp]: "hd (coeffs p) \<noteq> 0"
    by (induct p) auto
  from assms have  "\<not> even (coeff_sign_changes p)"
    by blast
  also have "even (coeff_sign_changes p) \<longleftrightarrow> sgn (hd (coeffs p)) = sgn (lead_coeff p)"
    by (auto simp add: even_sign_changes_iff last_coeffs_eq_coeff_degree)
  finally have "sgn (hd (coeffs p)) * sgn (lead_coeff p) < 0" 
    by (auto simp: sgn_if split: if_split_asm)
  also from \<open>p \<noteq> 0\<close> have "hd (coeffs p) = poly p 0" by (induction p) auto
  finally have "poly p 0 * lead_coeff p < 0" by (auto simp: mult_less_0_iff)

  from pos_root_exI[OF this] that show ?thesis by blast
qed

text \<open>
  We can now show the statement without the restriction to a non-zero constant coefficient.
  We can do this by simply factoring $p$ into the form $p \cdot x^n$, where $n$ is chosen as
  large as possible. This corresponds to stripping all initial zeros of the coefficient list,
  which obviously changes neither the existence of positive roots nor the number of coefficient 
  sign changes.
\<close>
lemma odd_coeff_sign_changes_imp_pos_roots:
  assumes "p \<noteq> (0 :: real poly)"
  assumes "odd (coeff_sign_changes p)"
  obtains x where "x > 0" "poly p x = 0"
  by sorry

end


subsection \<open>Proof of Descartes' sign rule\<close>

text \<open>
  For a polynomial $p(X) = a_0 + \ldots + a_n X^n$, we have 
  $[X^i] (1-X)p(X) = (\sum\limits_{j=0}^i a_j)$.
\<close>
lemma coeff_poly_times_one_minus_x:
  fixes g :: "'a :: linordered_idom poly"
  shows "coeff g n = (\<Sum>i\<le>n. coeff (g * [:1, -1:]) i)"
  by sorry

text \<open>
  We apply the previous lemma to the coefficient list of a polynomial and show: 
  given a polynomial $p(X)$ and $q(X) = (1 - X)p(X)$, the coefficient list of $p(X)$ is the 
  list of partial sums of the coefficient list of $q(X)$.
\<close>
lemma Poly_times_one_minus_x_eq_psums:
  fixes xs :: "'a :: linordered_idom list"
  assumes [simp]: "length xs = length ys"
  assumes "Poly xs = Poly ys * [:1, -1:]"
  shows   "ys = psums xs"
  by sorry

text \<open>
  We can now apply our main lemma on the sign changes in lists to the coefficient lists of 
  a nonzero polynomial $p(X)$ and $(1-X)p(X)$: the difference of the changes in the 
  coefficient lists is odd and positive.
\<close>
lemma sign_changes_poly_times_one_minus_x:
  fixes g :: "'a :: linordered_idom poly" and a :: 'a
  assumes nz: "g \<noteq> 0"
  defines "v \<equiv> coeff_sign_changes"
  shows "v ([:1, -1:] * g) - v g > 0 \<and> odd (v ([:1, -1:] * g) - v g)"
  by sorry

text \<open>
  We can now lift the previous lemma to the case of $p(X)$ and $(a-X)p(X)$ by substituting $X$ 
  with $aX$, yielding the polynomials $p(aX)$ and $a \cdot (1-X) \cdot p(aX)$.
\<close>
lemma sign_changes_poly_times_root_minus_x:
  fixes g :: "'a :: linordered_idom poly" and a :: 'a
  assumes nz: "g \<noteq> 0" and pos: "a > 0"
  defines "v \<equiv> coeff_sign_changes"
  shows "v ([:a, -1:] * g) - v g > 0 \<and> odd (v ([:a, -1:] * g) - v g)"
  by sorry

text \<open>
  Finally, the difference of the number of coefficient sign changes and the number of
  positive roots is non-negative and even. This follows straightforwardly by induction 
  over the roots.
\<close>
lemma descartes_sign_rule_aux:
  fixes p :: "real poly"
  assumes "p \<noteq> 0"
  shows   "coeff_sign_changes p \<ge> count_pos_roots p \<and> 
           even (coeff_sign_changes p - count_pos_roots p)"
  by sorry

text \<open>
  The main theorem is then an obvious consequence
\<close>
theorem descartes_sign_rule:
  fixes p :: "real poly"
  assumes "p \<noteq> 0"
  shows "\<exists>d. even d \<and> coeff_sign_changes p = count_pos_roots p + d"
  by sorry

end
