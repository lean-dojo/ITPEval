(* Title:       Proving the impossibility of trisecting an angle and doubling the cube
   Authors:     Ralph Romanos <ralph.romanos at student.ecp.fr> (2012),
                Lawrence Paulson <lp15 at cam.ac.uk> (2012)
   Maintainer:  Ralph Romanos <ralph.romanos at student.ecp.fr>
*)

section \<open>Proving the impossibility of trisecting an angle and doubling the cube\<close>

theory Impossible_Geometry
imports Complex_Main
begin

section \<open>Formal Proof\<close>

subsection \<open>Definition of the set of Points\<close>

datatype point = Point real real

definition points_def:
  "points = {M. \<exists> x \<in> \<real>. \<exists> y \<in> \<real>. (M = Point x y)}"

primrec abscissa :: "point => real"
  where abscissa: "abscissa (Point x y) = x"

primrec ordinate :: "point => real"
  where ordinate: "ordinate (Point x y) = y"

lemma point_surj [simp]:
  "Point (abscissa M) (ordinate M) = M"
  by sorry

lemma point_eqI [intro?]:
  "\<lbrakk>abscissa M = abscissa N; ordinate M = ordinate N\<rbrakk> \<Longrightarrow> M = N"
  by sorry

lemma point_eq_iff:
  "M = N \<longleftrightarrow> abscissa M = abscissa N \<and> ordinate M = ordinate N"
  by sorry

subsection \<open>Subtraction\<close>

text \<open>Datatype point has a structure of abelian group\<close>

instantiation point :: ab_group_add
begin

definition point_zero_def:
  "0 = Point 0 0"

definition point_one_def:
  "point_one = Point 1 0"

definition point_add_def:
  "A + B = Point (abscissa A + abscissa B) (ordinate A + ordinate B)"

definition point_minus_def:
  "- A = Point (- abscissa A) (- ordinate A)"

definition point_diff_def:
  "A - (B::point) = A + - B"

lemma Point_eq_0 [simp]:
  "Point xA yA = 0 \<longleftrightarrow> (xA = 0 \<and> yA = 0)"
  by sorry

lemma point_abscissa_zero [simp]:
  "abscissa 0 = 0"
  by sorry

lemma point_ordinate_zero [simp]:
  "ordinate 0 = 0"
  by sorry

lemma point_add [simp]:
  "Point xA yA + Point xB yB = Point (xA + xB) (yA + yB)"
  by sorry

lemma point_abscissa_add [simp]:
  "abscissa (A + B) = abscissa A + abscissa B"
  by sorry

lemma point_ordinate_add [simp]:
  "ordinate (A + B) = ordinate A + ordinate B"
  by sorry

lemma point_minus [simp]:
  "- (Point xA yA) = Point (- xA) (- yA)"
  by sorry

lemma point_abscissa_minus [simp]:
  "abscissa (- A) = - abscissa (A)"
  by sorry

lemma point_ordinate_minus [simp]:
  "ordinate (- A) = - ordinate (A)"
  by sorry

lemma point_diff [simp]:
  "Point xA yA - Point xB yB = Point (xA - xB) (yA - yB)"
  by sorry

lemma point_abscissa_diff [simp]:
  "abscissa (A - B) = abscissa (A) - abscissa (B)"
  by sorry

lemma point_ordinate_diff [simp]:
  "ordinate (A - B) = ordinate (A) - ordinate (B)"
  by sorry

instance
  by intro_classes (simp_all add: point_add_def point_diff_def)

end

subsection \<open>Metric Space\<close>

text \<open>We can also define a distance, hence point is also a metric space\<close>

instantiation point :: metric_space
begin

definition point_dist_def:
  "dist A B =  sqrt ((abscissa (A - B))^2 + (ordinate (A - B))^2)"

definition
  "(uniformity :: (point \<times> point) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition
  "open (S :: point set) = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lemma point_dist [simp]:
  "dist (Point xA yA) (Point xB yB) =  sqrt ((xA - xB)^2 + (yA - yB)^2)"
  by sorry

lemma real_sqrt_diff_squares_triangle_ineq:
  fixes a b c d :: real
  shows "sqrt ((a - c)^2 + (b - d)^2) \<le> sqrt (a^2 + b^2) + sqrt (c^2 + d^2)"
  by sorry

instance
proof
  fix A B C :: point and S :: "point set"
  show "(dist A B = 0) = (A = B)"
    by (induct A, induct B) (simp add: point_dist_def)
  show "(dist A B) \<le> (dist A C) + (dist B C)"
  proof -
    have "sqrt ((abscissa (A - B))^2 + (ordinate (A - B))^2) \<le>
          sqrt ((abscissa (A - C))^2 + (ordinate (A - C))^2) +
          sqrt ((abscissa (B - C))^2 + (ordinate (B - C))^2)"
      using real_sqrt_diff_squares_triangle_ineq
             [of "abscissa (A) - abscissa (C)" "abscissa (B) - abscissa (C)"
                 "ordinate (A) - ordinate (C)" "ordinate (B) - ordinate (C)"]
      by (simp only: point_diff_def) (simp add: algebra_simps)
    thus ?thesis
      by (simp add: point_dist_def)
  qed
qed (rule uniformity_point_def open_point_def)+
end

subsection \<open>Geometric Definitions\<close>

text \<open>These geometric definitions will later be used to define
constructible points\<close>

text \<open>The distance between two points is defined with the distance
of the metric space point\<close>
definition distance_def:
  "distance A B = dist A B"

text \<open>@{term "parallel A B C D"} is true if the lines @{term "(AB)"}
and @{term "(CD)"} are parallel. If not it is false.\<close>

definition parallel_def:
  "parallel A B C D = ((abscissa A - abscissa B) * (ordinate C - ordinate D) = (ordinate A - ordinate B) * (abscissa C - abscissa D))"

text \<open>Three points @{term "A B C"} are collinear if and only if the
lines @{term "(AB)"} and @{term "(AC)"} are parallel\<close>

definition collinear_def:
  "collinear A B C = parallel A B A C"

text \<open>The point @{term M} is the intersection of two lines @{term
"(AB)"} and @{term "(CD)"} if and only if the points @{term A}, @{term
M} and @{term B} are collinear and the points @{term C}, @{term M} and
@{term D} are also collinear\<close>

definition is_intersection_def:
  "is_intersection M A B C D = (collinear A M B \<and> collinear C M D)"


subsection \<open>Reals definable with square roots\<close>

text \<open>The inductive set @{term "radical_sqrt"} defines the reals
that can be defined with square roots. If @{term x} is in the
following set, then it depends only upon rational expressions and
square roots. For example, suppose @{term x} is of the form : $x =
(\sqrt{a + \sqrt{b}} + \sqrt{c + \sqrt{d*e +f}}) / (\sqrt{a} +
\sqrt{b}) + (a + \sqrt{b}) / \sqrt{g}$, where @{term a}, @{term b},
@{term c}, @{term d}, @{term e}, @{term f} and @{term g} are
rationals. Then @{term x} is in @{term "radical_sqrt"} because it is
only defined with rationals and square roots of radicals.\<close>

inductive_set radical_sqrt :: "real set"
  where
    Rat: "x \<in> \<rat> \<Longrightarrow> x \<in> radical_sqrt"
  | Neg: "x \<in> radical_sqrt \<Longrightarrow> -x \<in> radical_sqrt"
  | Inverse: "x \<in> radical_sqrt \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 1/x \<in> radical_sqrt"
  | Plus: "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> x+y \<in> radical_sqrt"
  | Times: "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> x*y \<in> radical_sqrt"
  | Sqrt: "x \<in> radical_sqrt \<Longrightarrow> x \<ge> 0 \<Longrightarrow> sqrt x \<in> radical_sqrt"

text \<open>Here, we list some rules that will be used to prove that a
given real is in @{term "radical_sqrt"}.\<close>

text \<open>Given two reals in @{term "radical_sqrt"} @{term x} and @{term
y}, the subtraction $x - y$ is also in @{term "radical_sqrt"}.\<close>

lemma radical_sqrt_rule_subtraction:
  "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> x-y \<in> radical_sqrt"
  by sorry


text \<open>Given two reals in @{term "radical_sqrt"} @{term x} and @{term
y}, and $y \neq 0$, the division $x / y$ is also in @{term
"radical_sqrt"}.\<close>

lemma radical_sqrt_rule_division:
  "\<lbrakk>x \<in> radical_sqrt; y \<in> radical_sqrt; y \<noteq> 0\<rbrakk> \<Longrightarrow> x/y \<in> radical_sqrt"
  by sorry


text \<open>Given a positive real @{term x} in @{term "radical_sqrt"}, its
square $x^2$ is also in @{term "radical_sqrt"}.\<close>

lemma radical_sqrt_rule_power2:
  "x \<in> radical_sqrt \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x^2 \<in> radical_sqrt"
  by sorry


text \<open>Given a positive real @{term x} in @{term "radical_sqrt"}, its
cube $x^3$ is also in @{term "radical_sqrt"}.\<close>

lemma radical_sqrt_rule_power3:
  "x \<in> radical_sqrt \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x^3 \<in> radical_sqrt"
  by sorry

subsection \<open>Introduction of the datatype expr which represents radical expressions\<close>

text \<open>An expression expr is either a rational constant: Const or the
negation of an expression or the inverse of an expression or the
addition of two expressions or the multiplication of two expressions
or the square root of an expression.\<close>

datatype expr = Const rat | Negation expr | Inverse expr | Addition expr expr | Multiplication expr expr | Sqrt expr

text \<open>The function @{term "translation"} translates a given
expression into its equivalent real.\<close>

fun translation :: "expr => real" (\<open>(2\<lbrace>_\<rbrace>)\<close>)
  where
  "translation (Const x) = of_rat x"|
  "translation (Negation e) = - translation e"|
  "translation (Inverse e) = (1::real) / translation e"|
  "translation (Addition e1 e2) = translation e1 + translation e2"|
  "translation (Multiplication e1 e2) = translation e1 * translation e2"|
  "translation (Sqrt e) = (if translation e < 0 then 0 else sqrt (translation e))"

text \<open>Define the set of all the radicals of a given expression. For
example, suppose @{term "expr"} is of the form : expr = Addition (Sqrt
(Addition (Const @{term a}) Sqrt (Const @{term b}))) (Sqrt (Addition
(Const @{term c}) (Sqrt (Sqrt (Const @{term d}))))), where @{term a},
@{term b}, @{term c} and @{term d} are rationals. This can be
translated as follows: \<open>\<lbrace>expr\<rbrace> =\<close>~$\sqrt{a + \sqrt{b}} +
\sqrt{c + \sqrt{\sqrt{d}}}$. Moreover, the set @{term "radicals"} of
this expression is : \<open>\<lbrace>\<close>Addition (Const @{term a}) (Sqrt
(Const @{term b})), Const @{term b}, Addition (Const @{term c}) (Sqrt
(Sqrt (Const @{term d}))), Sqrt (Const @{term d}), Const @{term
d}\<open>\<rbrace>\<close>.\<close>

fun radicals :: "expr => expr set"
  where
  "radicals (Const x) = {}"|
  "radicals (Negation e) = (radicals e)"|
  "radicals (Inverse e) = (radicals e)"|
  "radicals (Addition e1 e2) = ((radicals e1) \<union> (radicals e2))"|
  "radicals (Multiplication e1 e2) = ((radicals e1) \<union> (radicals e2))"|
  "radicals (Sqrt e) = (if \<lbrace>e\<rbrace> < 0 then radicals e else {e} \<union> (radicals e))"


text \<open>If @{term r} is in @{term "radicals"} of @{term e} then the
set @{term "radical_sqrt"} of @{term r} is a subset (strictly
speaking) of the set @{term "radicals"} of @{term e}.\<close>

lemma radicals_expr_subset: "r \<in> radicals e \<Longrightarrow> radicals r \<subset> radicals e"
  by sorry

text \<open>If @{term x} is in @{term "radical_sqrt"} then there exists a
radical expression @{term e} which translation is @{term x} (it is
important to notice that this expression is not necessarily
unique).\<close>

lemma radical_sqrt_correct_expr:
  "x \<in> radical_sqrt \<Longrightarrow> \<exists> e. \<lbrace>e\<rbrace> = x"
  by sorry

text \<open>The order of an expression is the maximum number of radicals
one over another occurring in a given expression. Using the example
above, suppose @{term "expr"} is of the form : expr = Addition (Sqrt
(Addition (Const @{term a}) Sqrt (Const @{term b}))) (Sqrt (Addition
(Const @{term c}) (Sqrt (Sqrt (Const @{term d}))))), where @{term a},
@{term b}, @{term c} and @{term d} are rationals and which can be
translated as follows: \<open>\<lbrace>expr\<rbrace> =\<close>~$\sqrt{a + \sqrt{b} +
\sqrt{c + \sqrt{\sqrt{d}}}}$. The order of @{term expr} is $max (2,3)
= 3$.\<close>

fun order :: "expr => nat"
  where
  "order (Const x) = 0"|
  "order (Negation e) = order e"|
  "order (Inverse e) = order e"|
  "order (Addition e1 e2) = max (order e1) (order e2)"|
  "order (Multiplication e1 e2) = max (order e1) (order e2)"|
  "order (Sqrt e) = 1 + order e"

text \<open>If an expression @{term s} is one of the radicals (or in
@{term "radicals"}) of the expression @{term r}, then its order is
smaller (strictly speaking) then the order of @{term r}.\<close>

lemma in_radicals_smaller_order:
  "s \<in> radicals r \<Longrightarrow> (order s) < (order r)"
  by sorry

text \<open>The following theorem is the converse of the previous lemma.\<close>

lemma in_radicals_smaller_order_contrap:
  "(order s) \<ge> (order r) \<Longrightarrow> \<not> (s \<in> radicals r)"
  by sorry

text \<open>An expression @{term r} cannot be one of its own radicals.\<close>

lemma not_in_own_radicals:
  "\<not> (r \<in> radicals r)"
  by sorry


text \<open>If an expression @{term e} is a radical expression and it has
no radicals then its translation is a rational.\<close>

lemma radicals_empty_rational: "radicals e = {} \<Longrightarrow> \<lbrace>e\<rbrace> \<in> \<rat>"
  by sorry

text \<open>A finite non-empty set of natural numbers has necessarily a
maximum.\<close>

lemma finite_set_has_max:
  "finite (s:: nat set) \<Longrightarrow> s \<noteq> {} \<Longrightarrow> \<exists>k \<in> s. \<forall> p \<in> s. p \<le> k"
  by sorry

text \<open>There is a finite number of radicals in an expression.\<close>

lemma finite_radicals: "finite (radicals e)"
  by sorry

text \<open>We define here a new set corresponding to the orders of each
element in the set @{term "radicals"} of an expression @{term
expr}. Using the example above, suppose @{term expr} is of the form :
expr = Addition (Sqrt (Addition (Const @{term a}) Sqrt (Const @{term
b}))) (Sqrt (Addition (Const @{term c}) (Sqrt (Sqrt (Const @{term
d}))))), where @{term a}, @{term b}, @{term c} and @{term d} are
rationals and which can be translated as follows: \<open>\<lbrace>expr\<rbrace>
=\<close>~$\sqrt{a + \sqrt{b}} + \sqrt{c + \sqrt{\sqrt{d}}}$. The set @{term
"radicals"} of @{term expr} is $\{$Addition (Const @{term a}) Sqrt
(Const @{term b}), Const @{term b}, Addition (Const @{term c}) (Sqrt
(Sqrt (Const @{term d}))), Sqrt (Const @{term d}), Const @{term
d}$\}$; therefore, the set @{term "order_radicals"} of this set is
$\{1,0,2,1,0\}$.\<close>

fun order_radicals:: "expr set => nat set"
  where "order_radicals s = {y. \<exists> x \<in> s. y = order x}"

text \<open>If the set of radicals of an expression @{term e} is not empty
and is finite then the set @{term "order_radicals"} of the set of
radicals of @{term e} is not empty and is also finite.\<close>

text \<open>The following lemma states that given an expression @{term e},
if the set @{term "order_radicals"} of the set @{term "radicals e"} is
not empty and is finite, then there exists a radical @{term r} of
@{term e} which is of highest order among the radicals of @{term e}.
\<close>

lemma finite_order_radicals_has_max:
  "\<lbrakk>order_radicals (radicals e) \<noteq> {};
     finite (order_radicals (radicals e))\<rbrakk>
    \<Longrightarrow> \<exists>r. r \<in> radicals e \<and> (\<forall>s\<in>radicals e. order s \<le> order r)"
  by sorry


text \<open>This important lemma states that in an expression that has at
least one radical, we can find an upmost radical @{term r} which is
not radical of any other term of the expression @{term e}. It is also
important to notice that this upmost radical is not necessarily unique
and is not the term of highest order of the expression @{term
e}. Using the example above, suppose @{term e} is of the form : @{term
e} = Addition (Sqrt (Addition (Const @{term a}) Sqrt (Const @{term
b}))) (Sqrt (Addition (Const @{term c}) (Sqrt (Sqrt (Const @{term
d}))))), where @{term a}, @{term b}, @{term c} and @{term d} are
rationals and which can be translated as follows: \<open>\<lbrace>e\<rbrace>
=\<close>~$\sqrt{a + \sqrt{b}} + \sqrt{c + \sqrt{\sqrt{d}}}$. The possible
upmost radicals in this expression are Addition (Const @{term a})
(Sqrt (Const @{term b})) or Addition (Const @{term c}) (Sqrt (Sqrt
(Const @{term d}))).\<close>


lemma finite_order_radicals:
  "radicals e \<noteq> {} \<Longrightarrow> finite (radicals e) \<Longrightarrow>
   order_radicals (radicals e) \<noteq> {} \<and> finite (order_radicals (radicals e))"
  by sorry

lemma upmost_radical_sqrt2:
  "radicals e \<noteq> {} \<Longrightarrow>
   \<exists>r \<in> radicals e. \<forall> s \<in> radicals e. r \<notin> radicals s"
  by sorry


text \<open>The following 7 lemmas are used to prove the main lemma @{term
"radical_sqrt_normal_form"} which states that if an expression @{term
e} has at least one radical then it can be written in a normal
form. This means that there exist three radical expressions @{term a},
@{term b} and @{term r} such that \<open>\<lbrace>e\<rbrace> = \<lbrace>a\<rbrace> + \<lbrace>b\<rbrace> *
\<sqrt>\<lbrace>r\<rbrace>\<close> and the radicals of @{term a} are radicals of @{term e}
but are not @{term r}, and the same goes for the radicals of @{term b}
and @{term r}. It is important to notice that @{term a}, @{term b} and
@{term r} are not unique and @{term "Sqrt r"} is not necessarily the
term of highest order.\<close>

lemma eq_sqrt_squared:
  "(x::real) \<ge> 0 \<Longrightarrow> (sqrt x) * (sqrt x) = x"
  by sorry

lemma radical_sqrt_normal_form_inverse:
  assumes "z \<ge> 0" "x \<noteq> y * sqrt z"
  shows
   "1 / (x + y * sqrt z) =
    x / (x * x - y * y * z) - (y * sqrt z) / (x * x - y * y * z)"
  by sorry

lemma radical_sqrt_normal_form_lemma:
  fixes e::expr
  assumes "radicals e \<noteq> {}"
  and "\<forall>s \<in> radicals e. r \<notin> radicals s"
  and "r \<in> radicals e"
  shows "\<exists>a b. 0 \<le> \<lbrace>r\<rbrace> \<and> \<lbrace>e\<rbrace> = \<lbrace>a\<rbrace> + \<lbrace>b\<rbrace> * sqrt \<lbrace>r\<rbrace> &
          radicals a \<union> radicals b \<union> radicals r \<subseteq> radicals e &
          r \<notin> radicals a \<union> radicals b"
       (is "\<exists>a b. ?concl e a b")
  by sorry

text \<open>This main lemma is essential for the remaining part of the proof.\<close>

theorem radical_sqrt_normal_form:
  "radicals e \<noteq> {} \<Longrightarrow>
   \<exists> r \<in> radicals e.
        \<exists> a b. \<lbrace>e\<rbrace> = \<lbrace>Addition a (Multiplication b (Sqrt r))\<rbrace> \<and> \<lbrace>r\<rbrace> \<ge> 0 \<and>
               radicals a \<union> radicals b \<union> radicals r \<subseteq> radicals e &
               r \<notin> radicals a \<union> radicals b \<union> radicals r"
  by sorry


subsection \<open>Important properties of the roots of a cubic equation\<close>

text \<open>The following 7 lemmas are used to prove a main result about
the properties of the roots of a cubic equation (@{term
"cubic_root_radical_sqrt_rational"}) which states that assuming that
@{term a} @{term b} and @{term c} are rationals and that @{term x} is
a radical satisfying $x^3 + a x^2 + b x + c = 0$ then there exists a
rational root. This lemma will be used in the proof of the
impossibility of trisection an angle and of duplicating a cube.\<close>


lemma cubic_root_radical_sqrt_steplemma:
  fixes P :: "real set"
  assumes Nats [THEN subsetD, intro]: "Nats \<subseteq> P"
  and Neg:  "\<forall>x \<in> P. -x \<in> P"
  and Inv:  "\<forall>x \<in> P. x \<noteq> 0 \<longrightarrow> 1/x \<in> P"
  and Add:  "\<forall>x \<in> P. \<forall>y \<in> P. x+y \<in> P"
  and Mult: "\<forall>x \<in> P. \<forall>y \<in> P. x*y \<in> P"
  and a: "a \<in> P" and b: "b \<in> P" and c: "c \<in> P"
  and eq0: "z^3 + a * z^2 + b * z + c = 0"
  and u: "u \<in> P"
  and v: "v \<in> P"
  and s: "s * s \<in> P"
  and z: "z = u + v * s"
  shows "\<exists>w \<in> P. w^3 + a * w^2 + b * w + c = 0"
  by sorry

lemma cubic_root_radical_sqrt_steplemma_sqrt:
  assumes Nats [THEN subsetD, intro]: "Nats \<subseteq> P"
  and "\<forall>x \<in> P. -x \<in> P"
  and "\<forall>x \<in> P. x \<noteq> 0 \<longrightarrow> 1/x \<in> P"
  and "\<forall>x \<in> P. \<forall>y \<in> P. x+y \<in> P"
  and "\<forall>x \<in> P. \<forall>y \<in> P. x*y \<in> P"
  and "(a \<in> P)" and b: "(b \<in> P)" and c: "(c \<in> P)"
  and "z^3 + a * z^2 + b * z + c = 0"
  and "u \<in> P" "v \<in> P" "s \<in> P"
  and "s \<ge> 0"
  and "z = u + v * sqrt s"
  shows "\<exists>w \<in> P. w^3 + a * w^2 + b * w + c = 0"
  by sorry

lemma cubic_root_radical_sqrt_lemma:
  fixes e::expr
  assumes a: "a \<in> \<rat>" and b: "b \<in> \<rat>" and c: "c \<in> \<rat>"
  and notEmpty: "radicals e \<noteq> {}"
  and eq0: "\<lbrace>e\<rbrace>^ 3 + a * \<lbrace>e\<rbrace>^2 + b * \<lbrace>e\<rbrace> + c = 0"
  shows "\<exists> e1. radicals e1 \<subset> radicals e \<and> (\<lbrace>e1\<rbrace>^3 + a * \<lbrace>e1\<rbrace>^2 + b * \<lbrace>e1\<rbrace> + c = 0)"
  by sorry

lemma cubic_root_radical_sqrt:
  assumes abc: "a \<in> \<rat>" "b \<in> \<rat>" "c \<in> \<rat>"
  shows "card (radicals e) = n \<Longrightarrow> \<lbrace>e\<rbrace>^3 + a * \<lbrace>e\<rbrace>^2 + b * \<lbrace>e\<rbrace> + c = 0 \<Longrightarrow>
         \<exists>x \<in> \<rat>. x^3 + a * x^2 + b * x + c = 0"
  by sorry

text \<open>Now we can prove the final result about the properties of the
roots of a cubic equation.\<close>

theorem cubic_root_radical_sqrt_rational:
  assumes a: "a \<in> \<rat>" and b: "b \<in> \<rat>" and c: "c \<in> \<rat>"
  and x: "x \<in> radical_sqrt"
  and x_eqn: "x^3 + a * x^2 + b * x + c = 0"
  shows c: "\<exists>x \<in> \<rat>. x^3 + a * x^2 + b * x + c = 0"
  by sorry

subsection \<open>Important properties of radicals\<close>

lemma sqrt_roots:
  "y^2=x \<Longrightarrow> x\<ge>0 \<and> (sqrt (x) = y | sqrt (x) = -y)"
  by sorry

lemma radical_sqrt_linear_equation:
  assumes "a \<in> radical_sqrt" "b \<in> radical_sqrt"
  and "\<not> (a = 0 \<and> b = 0)"
  and "a * x + b = 0"
  shows "x \<in> radical_sqrt"
  by sorry


lemma radical_sqrt_simultaneous_linear_equation:
  assumes "a \<in> radical_sqrt"
  and "b \<in> radical_sqrt"
  and "c \<in> radical_sqrt"
  and "d \<in> radical_sqrt"
  and "e \<in> radical_sqrt"
  and "f \<in> radical_sqrt"
  and NotNull: "\<not> (a*e - b*d =0 \<and> a*f - c*d = 0 \<and> e*c = b*f)"
  and eq: "a*x + b*y = c" "d*x + e*y = f"
  shows "x \<in> radical_sqrt \<and> y \<in> radical_sqrt"
  by sorry


lemma radical_sqrt_quadratic_equation:
  assumes "a \<in> radical_sqrt"
      and "b \<in> radical_sqrt"
      and "c \<in> radical_sqrt"
      and eq0: "a*x^2+b*x+c = 0"
      and NotNull: "\<not> (a = 0 \<and> b = 0 \<and> c = 0)"
  shows "x \<in> radical_sqrt"
  by sorry


lemma radical_sqrt_simultaneous_linear_quadratic:
  assumes "a \<in> radical_sqrt"
      and "b \<in> radical_sqrt"
      and "c \<in> radical_sqrt"
      and "d \<in> radical_sqrt"
      and "e \<in> radical_sqrt"
      and "f \<in> radical_sqrt"
      and NotNull: "\<not>(d=0 \<and> e=0 \<and> f=0)"
      and eq: "(x-a)^2 + (y-b)^2 = c""d*x+e*y = f"
  shows "x \<in> radical_sqrt \<and> y \<in> radical_sqrt"
  by sorry

lemma radical_sqrt_simultaneous_quadratic_quadratic:
  assumes "a \<in> radical_sqrt"
      and "b \<in> radical_sqrt"
      and "c \<in> radical_sqrt"
      and "d \<in> radical_sqrt"
      and "e \<in> radical_sqrt"
      and "f \<in> radical_sqrt"
      and NotEqual: "\<not> (a = d \<and> b = e \<and> c = f)"
      and eq: "(x - a)^2 + (y - b)^2 = c" "(x - d)^2 + (y - e)^2 = f"
  shows "x \<in> radical_sqrt \<and> y \<in> radical_sqrt"
  by sorry


subsection \<open>Important properties of geometrical points which coordinates are radicals\<close>

lemma radical_sqrt_line_line_intersection:
  assumes absA: "(abscissa (A)) \<in> radical_sqrt"
      and ordA: "(ordinate A) \<in> radical_sqrt"
      and absB: "(abscissa B) \<in> radical_sqrt"
      and ordB: "(ordinate B) \<in> radical_sqrt"
      and absC: "(abscissa C) \<in> radical_sqrt"
      and ordC: "(ordinate C) \<in> radical_sqrt"
      and absD: "(abscissa D) \<in> radical_sqrt"
      and ordD: "(ordinate D) \<in> radical_sqrt"
      and notParallel: "\<not> (parallel A B C D)"
      and isIntersec: "is_intersection X A B C D"
  shows "(abscissa X) \<in> radical_sqrt \<and> (ordinate X) \<in> radical_sqrt"
  by sorry


lemma radical_sqrt_line_circle_intersection:
  assumes absA: "(abscissa A) \<in> radical_sqrt" and ordA: "(ordinate A) \<in> radical_sqrt"
      and absB: "(abscissa B) \<in> radical_sqrt" and ordB: "(ordinate B) \<in> radical_sqrt"
      and absC: "(abscissa C) \<in> radical_sqrt" and ordC: "(ordinate C) \<in> radical_sqrt"
      and absD: "(abscissa D) \<in> radical_sqrt" and ordD: "(ordinate D) \<in> radical_sqrt"
      and absE: "(abscissa E) \<in> radical_sqrt" and ordE: "(ordinate E) \<in> radical_sqrt"
      and notEqual: "A \<noteq> B"
      and colin: "collinear A X B"
      and eqDist: "(distance C X = distance D E)"
shows "(abscissa X) \<in> radical_sqrt \<and> (ordinate X) \<in> radical_sqrt"
  by sorry


lemma radical_sqrt_circle_circle_intersection:
  assumes absA: "(abscissa A) \<in> radical_sqrt" and ordA: "(ordinate A) \<in> radical_sqrt"
      and absB: "(abscissa B) \<in> radical_sqrt" and ordB: "(ordinate B) \<in> radical_sqrt"
      and absC: "(abscissa C) \<in> radical_sqrt" and ordC: "(ordinate C) \<in> radical_sqrt"
      and absD: "(abscissa D) \<in> radical_sqrt" and ordD: "(ordinate D) \<in> radical_sqrt"
      and absE: "(abscissa E) \<in> radical_sqrt" and ordE: "(ordinate E) \<in> radical_sqrt"
      and absF: "(abscissa F) \<in> radical_sqrt" and ordF: "(ordinate F) \<in> radical_sqrt"
      and eqDist0: "distance A X = distance B C"
      and eqDist1: "distance D X = distance E F"
      and notEqual: "\<not> (A = D \<and> distance B C = distance E F)"
  shows "(abscissa X) \<in> radical_sqrt \<and> (ordinate X) \<in> radical_sqrt"
  by sorry

subsection \<open>Definition of the set of contructible points\<close>

inductive_set constructible :: "point set"
  where
  "(M \<in> points \<and> (abscissa M) \<in> \<rat> \<and> (ordinate M) \<in> \<rat>) \<Longrightarrow> M \<in> constructible"|
  "(A \<in> constructible \<and> B \<in> constructible \<and> C \<in> constructible \<and> D \<in> constructible \<and> \<not> parallel A B C D \<and> is_intersection M A B C D) \<Longrightarrow> M \<in> constructible"|
  "(A \<in> constructible \<and> B \<in> constructible \<and> C \<in> constructible \<and> D \<in> constructible \<and> E \<in> constructible \<and> \<not> A = B \<and> collinear A M B \<and> distance C M = distance D E) \<Longrightarrow> M \<in> constructible"|
  "(A \<in> constructible \<and> B \<in> constructible \<and> C \<in> constructible \<and> D \<in> constructible \<and> E \<in> constructible \<and> F \<in> constructible \<and> \<not> (A = D \<and> distance B C = distance E F) \<and> distance A M = distance B C \<and> distance D M = distance E F) \<Longrightarrow> M \<in> constructible"

subsection \<open>An important property about constructible points: their
coordinates are radicals\<close>

lemma constructible_radical_sqrt:
  assumes "M \<in> constructible"
  shows "(abscissa M) \<in> radical_sqrt \<and> (ordinate M) \<in> radical_sqrt"
  by sorry

subsection \<open>Proving the impossibility of duplicating the cube\<close>

lemma impossibility_of_doubling_the_cube_lemma:
  assumes x: "x \<in> radical_sqrt"
  and x_eqn: "x^3 = 2"
  shows False
  by sorry


theorem impossibility_of_doubling_the_cube:
  "x^3 = 2 \<Longrightarrow> (Point x 0) \<notin> constructible"
  by sorry


subsection \<open>Proving the impossibility of trisecting an angle\<close>

lemma impossibility_of_trisecting_pi_over_3_lemma:
  assumes x: "x \<in> radical_sqrt"
  and x_eqn: "x^3 - 3 * x - 1 = 0"
  shows False
  by sorry


theorem impossibility_of_trisecting_angle_pi_over_3:
  "Point (cos (pi / 9)) 0 \<notin> constructible"
  by sorry

end
