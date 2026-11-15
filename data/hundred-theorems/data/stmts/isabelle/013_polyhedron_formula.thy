section \<open>Euler's Polyhedron Formula\<close>

text \<open>One of the Famous 100 Theorems, ported from HOL Light\<close>
text\<open>Cited source:  
Lawrence, J. (1997). A Short Proof of Euler's Relation for Convex Polytopes. 
\emph{Canadian Mathematical Bulletin}, \textbf{40}(4), 471--474.\<close>

theory Euler_Formula
  imports 
    "HOL-Analysis.Analysis" 
begin


text\<open> Interpret which "side" of a hyperplane a point is on.                     \<close>

definition hyperplane_side
  where "hyperplane_side \<equiv> \<lambda>(a,b). \<lambda>x. sgn (a \<bullet> x - b)"

text\<open> Equivalence relation imposed by a hyperplane arrangement.                 \<close>

definition hyperplane_equiv
 where "hyperplane_equiv \<equiv> \<lambda>A x y. \<forall>h \<in> A. hyperplane_side h x = hyperplane_side h y"

lemma hyperplane_equiv_refl [iff]: "hyperplane_equiv A x x"
  by sorry

lemma hyperplane_equiv_sym:
   "hyperplane_equiv A x y \<longleftrightarrow> hyperplane_equiv A y x"
  by sorry

lemma hyperplane_equiv_trans:
   "\<lbrakk>hyperplane_equiv A x y; hyperplane_equiv A y z\<rbrakk> \<Longrightarrow> hyperplane_equiv A x z"
  by sorry

lemma hyperplane_equiv_Un:
   "hyperplane_equiv (A \<union> B) x y \<longleftrightarrow> hyperplane_equiv A x y \<and> hyperplane_equiv B x y"
  by sorry

subsection\<open> Cells of a hyperplane arrangement\<close>

definition hyperplane_cell :: "('a::real_inner \<times> real) set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "hyperplane_cell \<equiv> \<lambda>A C. \<exists>x. C = Collect (hyperplane_equiv A x)"

lemma hyperplane_cell: "hyperplane_cell A C \<longleftrightarrow> (\<exists>x. C = {y. hyperplane_equiv A x y})"
  by sorry

lemma not_hyperplane_cell_empty [simp]: "\<not> hyperplane_cell A {}"
  by sorry

lemma nonempty_hyperplane_cell: "hyperplane_cell A C \<Longrightarrow> (C \<noteq> {})"
  by sorry

lemma Union_hyperplane_cells: "\<Union> {C. hyperplane_cell A C} = UNIV"
  by sorry

lemma disjoint_hyperplane_cells:
   "\<lbrakk>hyperplane_cell A C1; hyperplane_cell A C2; C1 \<noteq> C2\<rbrakk> \<Longrightarrow> disjnt C1 C2"
  by sorry

lemma disjoint_hyperplane_cells_eq:
   "\<lbrakk>hyperplane_cell A C1; hyperplane_cell A C2\<rbrakk> \<Longrightarrow> (disjnt C1 C2 \<longleftrightarrow> (C1 \<noteq> C2))"
  by sorry

lemma hyperplane_cell_empty [iff]: "hyperplane_cell {} C \<longleftrightarrow> C = UNIV"
  by sorry

lemma hyperplane_cell_singleton_cases:
  assumes "hyperplane_cell {(a,b)} C"
  shows "C = {x. a \<bullet> x = b} \<or> C = {x. a \<bullet> x < b} \<or> C = {x. a \<bullet> x > b}"
  by sorry

lemma hyperplane_cell_singleton:
   "hyperplane_cell {(a,b)} C \<longleftrightarrow>
    (if a = 0 then C = UNIV else C = {x. a \<bullet> x = b} \<or> C = {x. a \<bullet> x < b} \<or> C = {x. a \<bullet> x > b})"
  by sorry

lemma hyperplane_cell_Un:
   "hyperplane_cell (A \<union> B) C \<longleftrightarrow>
        C \<noteq> {} \<and>
        (\<exists>C1 C2. hyperplane_cell A C1 \<and> hyperplane_cell B C2 \<and> C = C1 \<inter> C2)"
  by sorry

lemma finite_hyperplane_cells:
   "finite A \<Longrightarrow> finite {C. hyperplane_cell A C}"
  by sorry

lemma finite_restrict_hyperplane_cells:
   "finite A \<Longrightarrow> finite {C. hyperplane_cell A C \<and> P C}"
  by sorry

lemma finite_set_of_hyperplane_cells:
   "\<lbrakk>finite A; \<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C\<rbrakk> \<Longrightarrow> finite \<C>"
  by sorry

lemma pairwise_disjoint_hyperplane_cells:
   "(\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C) \<Longrightarrow> pairwise disjnt \<C>"
  by sorry

lemma hyperplane_cell_Int_open_affine:
  assumes "finite A" "hyperplane_cell A C"
  obtains S T where "open S" "affine T" "C = S \<inter> T"
  by sorry

lemma hyperplane_cell_relatively_open:
  assumes "finite A" "hyperplane_cell A C"
  shows "openin (subtopology euclidean (affine hull C)) C"
  by sorry

lemma hyperplane_cell_relative_interior:
   "\<lbrakk>finite A; hyperplane_cell A C\<rbrakk> \<Longrightarrow> rel_interior C = C"
  by sorry

lemma hyperplane_cell_convex:
  assumes "hyperplane_cell A C"
  shows "convex C"
  by sorry

lemma hyperplane_cell_Inter:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
    and "\<C> \<noteq> {}" and INT: "\<Inter>\<C> \<noteq> {}"
  shows "hyperplane_cell A (\<Inter>\<C>)"
  by sorry


lemma hyperplane_cell_Int:
   "\<lbrakk>hyperplane_cell A S; hyperplane_cell A T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> hyperplane_cell A (S \<inter> T)"
  by sorry

subsection\<open> A cell complex is considered to be a union of such cells\<close>

definition hyperplane_cellcomplex 
  where "hyperplane_cellcomplex A S \<equiv>
        \<exists>\<T>. (\<forall>C \<in> \<T>. hyperplane_cell A C) \<and> S = \<Union>\<T>"

lemma hyperplane_cellcomplex_empty [simp]: "hyperplane_cellcomplex A {}"
  by sorry

lemma hyperplane_cell_cellcomplex:
   "hyperplane_cell A C \<Longrightarrow> hyperplane_cellcomplex A C"
  by sorry

lemma hyperplane_cellcomplex_Union:
  assumes "\<And>S. S \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (\<Union> \<C>)"
  by sorry

lemma hyperplane_cellcomplex_Un:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S \<union> T)"
  by sorry

lemma hyperplane_cellcomplex_UNIV [simp]: "hyperplane_cellcomplex A UNIV"
  by sorry

lemma hyperplane_cellcomplex_Inter:
  assumes "\<And>S. S \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (\<Inter>\<C>)"
  by sorry

lemma hyperplane_cellcomplex_Int:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S \<inter> T)"
  by sorry

lemma hyperplane_cellcomplex_Compl:
  assumes "hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (- S)"
  by sorry

lemma hyperplane_cellcomplex_diff:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S - T)"
  by sorry

lemma hyperplane_cellcomplex_mono:
  assumes "hyperplane_cellcomplex A S" "A \<subseteq> B"
  shows "hyperplane_cellcomplex B S"
  by sorry

lemma finite_hyperplane_cellcomplexes:
  assumes "finite A"
  shows "finite {C. hyperplane_cellcomplex A C}"
  by sorry

lemma finite_restrict_hyperplane_cellcomplexes:
   "finite A \<Longrightarrow> finite {C. hyperplane_cellcomplex A C \<and> P C}"
  by sorry

lemma finite_set_of_hyperplane_cellcomplex:
  assumes "finite A" "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C"
  shows "finite \<C>"
  by sorry

lemma cell_subset_cellcomplex:
   "\<lbrakk>hyperplane_cell A C; hyperplane_cellcomplex A S\<rbrakk> \<Longrightarrow> C \<subseteq> S \<longleftrightarrow> ~ disjnt C S"
  by sorry


subsection \<open>Euler characteristic\<close>


definition Euler_characteristic :: "('a::euclidean_space \<times> real) set \<Rightarrow> 'a set \<Rightarrow> int"
  where "Euler_characteristic A S \<equiv>
        (\<Sum>C | hyperplane_cell A C \<and> C \<subseteq> S. (-1) ^ nat (aff_dim C))"

lemma Euler_characteristic_empty [simp]: "Euler_characteristic A {} = 0"
  by sorry

lemma Euler_characteristic_cell_Union:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
  shows "Euler_characteristic A (\<Union> \<C>) = (\<Sum>C\<in>\<C>. (- 1) ^ nat (aff_dim C))"
  by sorry

lemma Euler_characteristic_cell:
   "hyperplane_cell A C \<Longrightarrow> Euler_characteristic A C = (-1) ^ (nat(aff_dim C))"
  by sorry

lemma Euler_characteristic_cellcomplex_Un:
  assumes "finite A" "hyperplane_cellcomplex A S" 
    and AT: "hyperplane_cellcomplex A T" and "disjnt S T"
  shows "Euler_characteristic A (S \<union> T) =
         Euler_characteristic A S + Euler_characteristic A T"
  by sorry

lemma Euler_characteristic_cellcomplex_Union:
  assumes "finite A" 
    and \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C" "pairwise disjnt \<C>"
  shows "Euler_characteristic A (\<Union> \<C>) = sum (Euler_characteristic A) \<C>"
  by sorry

lemma Euler_characteristic:
  fixes A :: "('n::euclidean_space * real) set"
  assumes "finite A"
  shows "Euler_characteristic A S =
        (\<Sum>d = 0..DIM('n). (-1) ^ d * int (card {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}))"
        (is "_ = ?rhs")
  by sorry

subsection \<open>Show that the characteristic is invariant w.r.t. hyperplane arrangement.\<close>

lemma hyperplane_cells_distinct_lemma:
   "{x. a \<bullet> x = b} \<inter> {x. a \<bullet> x < b} = {} \<and>
         {x. a \<bullet> x = b} \<inter> {x. a \<bullet> x > b} = {} \<and>
         {x. a \<bullet> x < b} \<inter> {x. a \<bullet> x = b} = {} \<and>
         {x. a \<bullet> x < b} \<inter> {x. a \<bullet> x > b} = {} \<and>
         {x. a \<bullet> x > b} \<inter> {x. a \<bullet> x = b} = {} \<and>
         {x. a \<bullet> x > b} \<inter> {x. a \<bullet> x < b} = {}"
  by sorry

proposition Euler_characterstic_lemma:
  assumes "finite A" and "hyperplane_cellcomplex A S"
  shows "Euler_characteristic (insert h A) S = Euler_characteristic A S"
  by sorry


lemma Euler_characterstic_invariant_aux:
  assumes "finite B" "finite A" "hyperplane_cellcomplex A S" 
  shows "Euler_characteristic (A \<union> B) S = Euler_characteristic A S"
  by sorry

lemma Euler_characterstic_invariant:
  assumes "finite A" "finite B" "hyperplane_cellcomplex A S" "hyperplane_cellcomplex B S"
  shows "Euler_characteristic A S = Euler_characteristic B S"
  by sorry

lemma Euler_characteristic_inclusion_exclusion:
  assumes "finite A" "finite \<S>" "\<And>K. K \<in> \<S> \<Longrightarrow> hyperplane_cellcomplex A K"
  shows "Euler_characteristic A (\<Union> \<S>) = (\<Sum>\<T> | \<T> \<subseteq> \<S> \<and> \<T> \<noteq> {}. (- 1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))"
  by sorry



subsection \<open>Euler-type relation for full-dimensional proper polyhedral cones\<close>

lemma Euler_polyhedral_cone:
  fixes S :: "'n::euclidean_space set"
  assumes "polyhedron S" "conic S" and intS: "interior S \<noteq> {}" and "S \<noteq> UNIV"
  shows "(\<Sum>d = 0..DIM('n). (- 1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 0"  (is "?lhs = 0")
  by sorry



subsection \<open>Euler-Poincare relation for special $(n-1)$-dimensional polytope\<close>

lemma Euler_Poincare_lemma:
  fixes p :: "'n::euclidean_space set"
  assumes "DIM('n) \<ge> 2" "polytope p" "i \<in> Basis" and affp: "affine hull p = {x. x \<bullet> i = 1}"
  shows "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d})) = 1"
  by sorry


corollary Euler_poincare_special:
  fixes p :: "'n::euclidean_space set"
  assumes "2 \<le> DIM('n)" "polytope p" "i \<in> Basis" and affp: "affine hull p = {x. x \<bullet> i = 0}"
  shows "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = d}) = 1"
  by sorry


subsection \<open>Now Euler-Poincare for a general full-dimensional polytope\<close>

theorem Euler_Poincare_full:
  fixes p :: "'n::euclidean_space set"
  assumes "polytope p" "aff_dim p = DIM('n)"
  shows "(\<Sum>d = 0..DIM('n). (-1) ^ d * (card {f. f face_of p \<and> aff_dim f = d})) = 1"
  by sorry


text \<open>In particular, the Euler relation in 3 dimensions\<close>
corollary Euler_relation:
  fixes p :: "'n::euclidean_space set"
  assumes "polytope p" "aff_dim p = 3" "DIM('n) = 3"
  shows "(card {v. v face_of p \<and> aff_dim v = 0} + card {f. f face_of p \<and> aff_dim f = 2}) - card {e. e face_of p \<and> aff_dim e = 1} = 2"
  by sorry

end