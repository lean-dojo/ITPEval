(* 
  File:    Liouville_Numbers.thy
  Author:  Manuel Eberl <manuel@pruvisto.org>

  The definition of Liouville numbers and their standard construction, plus the proof
  that any Liouville number is transcendental.
*)

theory Liouville_Numbers
imports 
  Complex_Main
  "HOL-Computational_Algebra.Polynomial"
  Liouville_Numbers_Misc
begin

(* 
  TODO: Move definition of algebraic numbers out of Algebraic_Numbers to reduce unnecessary
  dependencies.
*)

text \<open>
A Liouville number is a real number that can be approximated well -- but not perfectly -- 
by a sequence of rational numbers. ``Well``, in this context, means that the error of the
 $n$-th rational in the sequence is bounded by the $n$-th power of its denominator.

Our approach will be the following:
\begin{itemize}
\item Liouville numbers cannot be rational.
\item Any irrational algebraic number cannot be approximated in the Liouville sense
\item Therefore, all Liouville numbers are transcendental.
\item The standard construction fulfils all the properties of Liouville numbers.
\end{itemize}
\<close>

subsection \<open>Definition of Liouville numbers\<close>

text \<open>
  The following definitions and proofs are largely adapted from those in the Wikipedia
  article on Liouville numbers.~\<^cite>\<open>"wikipedia"\<close>
\<close>

text \<open>
  A Liouville number is a real number that can be approximated well -- but not perfectly --
  by a sequence of rational numbers. The error of the $n$-th term $\frac{p_n}{q_n}$ is at most
  $q_n^{-n}$, where $p_n\in\isasymint$ and $q_n \in\isasymint_{\geq 2}$.

  We will say that such a number can be approximated in the Liouville sense.
\<close>
locale liouville =
  fixes x :: real and p q :: "nat \<Rightarrow> int"
  assumes approx_int_pos: "abs (x - p n / q n) > 0" 
      and denom_gt_1:     "q n > 1"
      and approx_int:     "abs (x - p n / q n) < 1 / of_int (q n) ^ n"

text \<open>
  First, we show that any Liouville number is irrational.
\<close>
lemma (in liouville) irrational: "x \<notin> \<rat>"
  by sorry


text \<open>
  Next, any irrational algebraic number cannot be approximated with rational 
  numbers in the Liouville sense.
\<close>
lemma liouville_irrational_algebraic:
  fixes x :: real
  assumes irrationsl: "x \<notin> \<rat>" and "algebraic x"
  obtains c :: real and n :: nat
    where "c > 0" and "\<And>(p::int) (q::int). q > 0 \<Longrightarrow> abs (x - p / q) > c / of_int q ^ n"
  by sorry


text \<open>
  Since Liouville numbers are irrational, but can be approximated well by rational 
  numbers in the Liouville sense, they must be transcendental.
\<close>
lemma (in liouville) transcendental: "\<not>algebraic x"
  by sorry


subsection \<open>Standard construction for Liouville numbers\<close>

text \<open>
  We now define the standard construction for Liouville numbers.
\<close>
definition standard_liouville :: "(nat \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> real" where
  "standard_liouville p q = (\<Sum>k. p k / of_int q ^ fact (Suc k))"

lemma standard_liouville_summable:
  fixes p :: "nat \<Rightarrow> int" and q :: int
  assumes "q > 1" "range p \<subseteq> {0..<q}"
  shows   "summable (\<lambda>k. p k / of_int q ^ fact (Suc k))"
  by sorry

lemma standard_liouville_sums:
  assumes "q > 1" "range p \<subseteq> {0..<q}"
  shows   "(\<lambda>k. p k / of_int q ^ fact (Suc k)) sums standard_liouville p q"
  by sorry


text \<open>
  Now we prove that the standard construction indeed yields Liouville numbers.
\<close>
lemma standard_liouville_is_liouville:
  assumes "q > 1" "range p \<subseteq> {0..<q}" "frequently (\<lambda>n. p n \<noteq> 0) sequentially"
  defines "b \<equiv> \<lambda>n. q ^ fact (Suc n)"
  defines "a \<equiv> \<lambda>n. (\<Sum>k\<le>n. p k * q ^ (fact (Suc n) - fact (Suc k)))"
  shows   "liouville (standard_liouville p q) a b"
  by sorry


text \<open>
  We can now show our main result: any standard Liouville number is transcendental.
\<close>
theorem transcendental_standard_liouville:
  assumes "q > 1" "range p \<subseteq> {0..<q}" "frequently (\<lambda>k. p k \<noteq> 0) sequentially"
  shows   "\<not>algebraic (standard_liouville p q)"
  by sorry

text \<open>
  In particular: The the standard construction for constant sequences, such as the
  ``classic'' Liouville constant $\sum_{n=1}^\infty 10^{-n!} = 0.11000100\ldots$,
  are transcendental. 

  This shows that Liouville numbers exists and therefore gives a concrete and 
  elementary proof that transcendental numbers exist.
\<close>
corollary transcendental_standard_standard_liouville:
  "a \<in> {0<..<b} \<Longrightarrow> \<not>algebraic (standard_liouville (\<lambda>_. int a) (int b))"
  by sorry

corollary transcendental_liouville_constant:
  "\<not>algebraic (standard_liouville (\<lambda>_. 1) 10)"
  by sorry

end
