theory Cube_Dissection
  imports Complex_Main "HOL-Library.Disjoint_Sets" "HOL-Library.Infinite_Set"
begin

text "Proof that a cube can't be dissected into a finite number of subcubes of different size
This formalization is heavily inspired by the Lean proof of the same fact,  \<^cite>\<open>leanproof\<close>.
One goal of this project, is that by restricting to cubes of dimension 3 the logic will
be easier to follow"

section "Basic definitions"
subsection "point and cube definitions"
record point = px:: real py::real pz::real
record cube = point:: point width::real
datatype axis = x | y | z
abbreviation "coordinate \<equiv> case_axis px py pz"

abbreviation is_valid :: "cube \<Rightarrow> bool" where "is_valid c \<equiv> (width c > 0)"

text "Min value of cube along given axis"
hide_const (open) min
abbreviation min :: "axis \<Rightarrow> cube \<Rightarrow> real" where "min ax c \<equiv> coordinate ax (point c)"

text "Max value (supremum) along given axis"
hide_const (open) max
abbreviation max :: "axis \<Rightarrow> cube \<Rightarrow> real" where "max ax c \<equiv> min ax c  + width c"

text "Sides of a cube. Half-open intervals, so that a dissection both is a cover, and consists of disjoint cubes"
abbreviation side :: "axis \<Rightarrow> cube \<Rightarrow> real set" where
  "side ax c \<equiv> {min ax c ..< max ax c}"

text "Sets of points generated from cubes"
definition to_set :: "cube \<Rightarrow> point set" where
  "to_set c = {p. px p \<in> side x c \<and> py p \<in> side y c \<and> pz p \<in> side z c}"
definition bot :: "cube \<Rightarrow> point set" where
  "bot c = {p. px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = min z c}"
definition top :: "cube \<Rightarrow> point set" where
  "top c = {p. px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = max z c}"

text "Moves a cube its width down (so top face to bottom face)"
definition shift_down :: "cube \<Rightarrow> cube" where 
  "shift_down c = c \<lparr> point := point c \<lparr> pz := min z c - width c  \<rparr> \<rparr>"


subsection "Calculations with sets from cubes"
text "A bunch of statements we need about how cubes can be compared by \<^term>\<open>side\<close>"
lemma top_shift_down_eq_bot: "top (shift_down c) = bot c"
  by sorry

text "Sets not empty"
lemma non_empty: "is_valid c \<Longrightarrow> to_set c \<noteq> {}"
  by sorry
lemma top_non_empty: "is_valid c \<Longrightarrow> top c \<noteq> {}"
  by sorry

text "\<^term>\<open>min\<close> of a cube is in corresponding \<^term>\<open>side\<close>"
lemma min_in_side: "is_valid c \<Longrightarrow> min ax c \<in> side ax c"
  by sorry

lemma min_ne_max: "is_valid c \<Longrightarrow> min ax c \<noteq> max ax c"
  by sorry
lemma min_lt_max: "is_valid c \<Longrightarrow> min ax c < max ax c"
  by sorry

lemma bot_subset: "bot c \<subseteq> to_set c"
  by sorry


subsubsection "Point membership"
text "Points in a cube's set, by looking at membership of \<^term>\<open>side\<close>"
lemma in_set_by_side: "p \<in> to_set c \<longleftrightarrow>
  px p \<in> side x c \<and> py p \<in> side y c \<and> pz p \<in> side z c"
  by sorry
lemma in_set_by_side_2: "\<lparr>px=x0, py=y0, pz=z0\<rparr> \<in> to_set c \<longleftrightarrow>
  x0 \<in> side x c \<and> y0 \<in> side y c \<and> z0 \<in> side z c"
  by sorry

lemma in_bot_by_side: "p \<in> bot c \<longleftrightarrow>
  px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = min z c"
  by sorry
lemma in_bot_by_side_2: "\<lparr>px=x0, py=y0, pz=z0\<rparr> \<in> bot c \<longleftrightarrow>
  x0 \<in> side x c \<and> y0 \<in> side y c \<and> z0 = min z c"
  by sorry

lemma in_top_by_side: "p \<in> top c \<longleftrightarrow>
  px p \<in> side x c \<and> py p \<in> side y c \<and> pz p = max z c"
  by sorry
lemma in_top_by_side_2: "\<lparr>px=x0, py=y0, pz=z0\<rparr> \<in> top c \<longleftrightarrow>
  x0 \<in> side x c \<and> y0 \<in> side y c \<and> z0 = max z c"
  by sorry

lemma all_point_iff: "(\<forall>p. P p) \<longleftrightarrow> (\<forall>x1 y1 z1. P \<lparr>px = x1, py = y1, pz = z1\<rparr>)"
  by sorry

text "Intersection by \<^term>\<open>side\<close>"
lemma set_intersect_by_side: "to_set c1 \<inter> to_set c2 \<noteq> {} \<longleftrightarrow>
  side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> side z c1 \<inter> side z c2 \<noteq> {}"
  by sorry

lemma bot_intersect_by_side: "bot c1 \<inter> bot c2 \<noteq> {} 
  \<longleftrightarrow> side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = min z c2"
  by sorry

lemma bot_top_intersect_by_side: "bot c1 \<inter> top c2 \<noteq> {} 
  \<longleftrightarrow> side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {} \<and> min z c1 = max z c2"
  by sorry


subsubsection "Cubes subset of each other, by \<^term>\<open>side\<close>"
lemma set_subset_by_side: "to_set c1 \<subseteq> to_set c2 \<longleftrightarrow>
  side x c1 \<subseteq> side x c2 \<and> side y c1 \<subseteq> side y c2 \<and> side z c1 \<subseteq> side z c2"
  by sorry
lemma set_eq_by_side: "to_set c1 = to_set c2 \<longleftrightarrow>
  side x c1 = side x c2 \<and> side y c1 = side y c2 \<and> side z c1 = side z c2"
  by sorry

lemma bot_eq_by_side: "is_valid c1 \<Longrightarrow> bot c1 = bot c2 \<longleftrightarrow>
side x c1 = side x c2 \<and> side y c1 = side y c2 \<and> min z c1 = min z c2"
  by sorry


lemma bot_top_subset_by_side: "is_valid c1 \<Longrightarrow> bot c1 \<subseteq> top c2 \<longleftrightarrow>
side x c1 \<subseteq> side x c2 \<and> side y c1 \<subseteq> side y c2 \<and> min z c1 = max z c2"
  by sorry
lemma bot_top_eq_by_side: "is_valid c1 \<Longrightarrow> bot c1 = top c2 \<longleftrightarrow>
side x c1 = side x c2 \<and> side y c1 = side y c2 \<and> min z c1 = max z c2"
  by sorry

lemma width_eq_if_side_eq: "\<lbrakk>is_valid c1; side ax c1 = side ax c2\<rbrakk> \<Longrightarrow> width c1 = width c2"
  by sorry

text "\<^term>\<open>to_set\<close> is injective"
lemma to_set_inj: 
  assumes "is_valid c1" "to_set c1 = to_set c2" 
  shows "c1 = c2"
  by sorry

text "\<^term>\<open>bot\<close> is also injective"
lemma bot_inj: assumes "is_valid c1" "bot c1 = bot c2" shows "c1 = c2"
  by sorry


section "Cubing"
text "We in this section introduce a dissection C of the unit cube"

text "The cube we show there is no dissection of"
definition unit_cube where "unit_cube = \<lparr> point=\<lparr>px=0, py=0, pz=0\<rparr>, width=1\<rparr>"

lemma min_unit_cube_0: "min ax unit_cube = 0"
  by sorry

lemma unit_cube_valid[simp]: "is_valid unit_cube"
  by sorry

text "What we want to show doesn't exist. \<^term>\<open>C\<close> is a set of cubes which satisfy:
\<^enum> All cubes are valid (width > 0)
\<^enum> All cubes a disjoint
\<^enum> The union of the cubes in \<^term>\<open>C\<close> equal \<^term>\<open>unit_cube\<close> (hence, all cubes are contained in \<^term>\<open>unit_cube\<close>)
\<^enum> All cubes in \<^term>\<open>C\<close> have different width
\<^enum> There are at least two cubes in \<^term>\<open>C\<close>
\<^enum> There are a finite number of cubes in \<^term>\<open>C\<close>"
definition is_dissection :: "cube set \<Rightarrow> bool" where
  "is_dissection C \<longleftrightarrow> 
  (\<forall> c \<in> C. is_valid c)
  \<and> disjoint (image to_set C)
  \<and> \<Union>(image to_set C) = to_set unit_cube
  \<and> inj_on width C \<comment> \<open>All cubes are of different size\<close>
  \<and> card C \<ge> 2  \<comment> \<open>At least two cubes\<close>
  \<and> finite C"

text "From now on, C is some fixed dissection of \<^term>\<open>unit_cube\<close>, and 'dissection' refers to this fact" 
context fixes C assumes dissection: "is_dissection C"
begin

subsection "Properties of \<^term>\<open>is_dissection\<close>"
lemma valid_if_dissection[simp]: "c \<in> C \<Longrightarrow> is_valid c"
  by sorry

lemma side_unit_cube: 
  "side ax unit_cube = {0..<1}"
  by sorry

lemma subset_unit_cube_if_dissection: "c \<in> C \<Longrightarrow> to_set c \<subseteq> to_set unit_cube"
  by sorry

lemma subset_unit_cube_by_side:
  "c \<in> C \<Longrightarrow> side ax c \<subseteq> {0..<1}"
  by sorry

lemma eq_iff_intersect: "\<lbrakk>c1 \<in> C; c2 \<in> C\<rbrakk> \<Longrightarrow> c1 = c2 \<longleftrightarrow> to_set c1 \<inter> to_set c2 \<noteq> {}"
  by sorry

text "Whenever we have a point in \<^term>\<open>unit_cube\<close>, there exists a (unique) cube in \<^term>\<open>C\<close> containing that
point"
lemma obtain_cube: "p \<in> to_set unit_cube \<Longrightarrow> \<exists> c \<in> C. p \<in> to_set c"
  by sorry

text "If the top of \<^term>\<open>c\<close> doesn't touch the top of \<^term>\<open>unit_cube\<close>, then top of \<^term>\<open>c\<close> must 
be covered by bottoms of cubes in \<^term>\<open>C\<close>"
lemma top_cover_by_bot:
  assumes "c \<in> C" "max z c < 1"
  shows "top c \<subseteq> \<Union>(image bot C)"
  by sorry


section "Hole"
text "A hole \<^term>\<open>h\<close> is a special kind of cube, where any cube whose bottom 'touches' the top of \<^term>\<open>v\<close>
must in fact have its bottom contained in the top of \<^term>\<open>v\<close>. If \<^term>\<open>h \<in> C\<close>, then this happens because 
all the other cubes surrounding \<^term>\<open>h\<close> go up taller, forming a hole on top of \<^term>\<open>v\<close>.
Note that we don't require that \<^term>\<open>h \<in> C\<close>, but this is only so we can prove that \<^term>\<open>unit_cube\<close>
shifted down by 1 is a hole - all other holes will in fact lie in \<^term>\<open>C\<close>. The concept of a hole is
inspired by the 'Valley' definition from \<^cite>\<open>leanproof\<close>"
subsection "Definitions"
definition is_hole :: "cube \<Rightarrow> bool" where
  "is_hole h \<longleftrightarrow>
    is_valid h
    \<and> top h \<subseteq> \<Union>(image bot C)
    \<and> (\<forall> c \<in> C .  bot c \<inter> top h \<noteq> {} \<longrightarrow> bot c \<subseteq> top h)
    \<comment> \<open>\<^term>\<open>v\<close> could be a cube in \<^term>\<open>C\<close> (and most often is), but any other cube must be different width.
        Also, this assumption is not actually needed (as it follows from \<^term>\<open>v\<close>, \<^term>\<open>c \<in> C\<close>), 
        but without it we have to do a special-case proof for the bottom of the \<^term>\<open>unit_cube\<close>\<close>
    \<and> (\<forall> c \<in> C . c \<noteq> h \<longrightarrow> width c \<noteq> width h)"

text "Subset of \<^term>\<open>C\<close> which are on a given hole h"
definition is_on_hole :: "cube \<Rightarrow> cube \<Rightarrow> bool" where
  "is_on_hole h c \<longleftrightarrow> bot c \<subseteq> top h"
definition filter_on_hole :: "cube \<Rightarrow> cube set" where
  "filter_on_hole h = Set.filter (is_on_hole h) C"


subsection "Properties of a hole"
text "Terminology: 
  'on hole' means cube \<^term>\<open>c\<close> with:  \<^term>\<open>bot c \<subseteq> top h\<close>. 
  'in hole' means point \<^term>\<open>p\<close> with: \<^term>\<open>p \<in> top h\<close> h"

text "\<^term>\<open>filter_on_hole h \<subseteq> C\<close>"
lemma dissection_if_on_hole[simp]: "c \<in> filter_on_hole h \<Longrightarrow> c \<in> C"
  by sorry

text "Holes, and cubes on them, are valid"
lemma valid_if_hole[simp]: "is_hole h \<Longrightarrow> is_valid h"
  by sorry
lemma valid_if_on_hole[simp]: "c \<in> filter_on_hole h \<Longrightarrow> is_valid c"
  by sorry

lemma on_hole_finite: "is_hole h \<Longrightarrow> finite (filter_on_hole h)"
  by sorry

lemma on_hole_if_in_filter_on_hole: "c \<in> filter_on_hole h \<Longrightarrow> is_on_hole h c"
  by sorry

lemma on_hole_cover: assumes "is_hole h" shows "top h \<subseteq> \<Union>(image bot (filter_on_hole h))"
  by sorry

text "Whenever we have a point \<^term>\<open>p\<close> in the top of a hole \<^term>\<open>h\<close>, there exists a (unique) cube 
\<^term>\<open>c \<in> filter_on_hole h\<close>, such that \<^term>\<open>p \<in> bot c\<close>"
lemma obtain_cube_if_in_hole: "\<lbrakk>is_hole h; p \<in> top h\<rbrakk> 
  \<Longrightarrow> \<exists>c \<in> filter_on_hole h . p \<in> bot c"
  by sorry

lemma on_hole_inj_on_width: "is_hole h \<Longrightarrow> inj_on width (filter_on_hole h)"
  by sorry


subsection "Properties of cubes on a hole"
lemma neq_hole_if_on_hole: "c \<in> filter_on_hole h \<Longrightarrow> c \<noteq> h"
  by sorry

lemma subset_if_on_hole: "c \<in> filter_on_hole h \<Longrightarrow> bot c \<subseteq> top h"
  by sorry

lemma side_subset_if_on_hole: "\<lbrakk>c \<in> filter_on_hole h; ax \<in> {x,y}\<rbrakk> \<Longrightarrow> side ax c \<subseteq> side ax h"
  by sorry

lemma min_z_eq_max_z_hole_if_on_hole:
  "c \<in> filter_on_hole h \<Longrightarrow> min z c =  max z h"
  by sorry

lemma z_eq_if_on_hole:
  "\<lbrakk>c1 \<in> filter_on_hole h; c2 \<in> filter_on_hole h\<rbrakk> \<Longrightarrow> min z c1 = min z c2"
  by sorry

text "Do not need to care about \<^term>\<open>z\<close>-coordinate"
lemma eq_iff_side_eq_if_on_hole: "\<lbrakk>c1 \<in> filter_on_hole h; c2 \<in> filter_on_hole h\<rbrakk> 
  \<Longrightarrow> c1 = c2 \<longleftrightarrow> side x c1 = side x c2 \<and> side y c1 = side y c2"
  by sorry

text "Disjointness-lemmas:"
lemma eq_iff_bot_intersect_if_on_hole: 
  assumes "c1 \<in> filter_on_hole h" "c2 \<in> filter_on_hole h"
  shows "c1 = c2 \<longleftrightarrow> bot c1 \<inter> bot c2 \<noteq> {}"
  by sorry

lemma eq_iff_side_intersect_if_on_hole: 
  "\<lbrakk>c1 \<in> filter_on_hole h; c2 \<in> filter_on_hole h\<rbrakk> 
  \<Longrightarrow> c1 = c2 \<longleftrightarrow> side x c1 \<inter> side x c2 \<noteq> {} \<and> side y c1 \<inter> side y c2 \<noteq> {}"
  by sorry

lemma width_on_hole_lt_width_hole: 
  assumes "is_hole h" "c \<in> filter_on_hole h" shows "width c < width h"
  by sorry

lemma strict_subset_if_on_hole: assumes "is_hole h" "c \<in> filter_on_hole h"
  shows "bot c \<subset> top h"
  by sorry

lemma on_hole_non_empty: "is_hole h \<Longrightarrow> filter_on_hole h \<noteq> {}"
  by sorry


section "Bottom of \<^term>\<open>unit_cube\<close> is a hole"
lemma bot_unit_cube_cover_by_bot: "bot unit_cube \<subseteq> \<Union>(image bot C)"
  by sorry

lemma eq_if_width_eq_if_subset:
  assumes "width c1 = width c2" "to_set c1 \<subseteq> to_set c2"
  shows "to_set c1 = to_set c2"
  by sorry

lemma width_ne_one:
  assumes "c \<in> C"
  shows "width c \<noteq> 1"
  by sorry

text "Combines the previous lemmas, to show that the bottom of \<^term>\<open>unit_cube\<close> is a hole"
proposition hole_unit_cube: "is_hole (shift_down unit_cube)"
  by sorry


section "Minimum cube on hole is interior"
context 
  fixes h assumes hole: "is_hole h"
begin

text "For this section, we fix a hole \<^term>\<open>h\<close>, and define \<^term>\<open>cmin\<close> to be the smallest cube 
on this hole. Theorem @{thm[source] hole} refers to this fact. The goal of this section is then to show that
\<^term>\<open>cmin\<close> itself is a hole." 

subsection "Definition: Minimum cube on \<^term>\<open>h\<close>"
text "\<^term>\<open>cmin\<close> is the smallest cube on the hole \<^term>\<open>h\<close>"
definition cmin:: "cube"
  where "cmin = (ARG_MIN width c . c \<in> filter_on_hole h)"

lemma arg_min_exist: "\<lbrakk>finite C'; C' \<noteq> {}\<rbrakk> \<Longrightarrow> (ARG_MIN width c . c \<in> C') \<in> C'"
  by sorry

text "This lemma also shows that \<^term>\<open>cmin\<close> exists"
lemma cmin_on_h: "cmin \<in> filter_on_hole h"
  by sorry

lemma cmin_valid[simp]: "is_valid cmin"
  by sorry

lemma arg_min_minimal: "\<lbrakk>finite C'; c \<in> C'\<rbrakk> \<Longrightarrow> width (ARG_MIN width c . c \<in> C') \<le> width c"
  by sorry

lemma cmin_minimal: "c \<in> filter_on_hole h \<Longrightarrow> width cmin \<le> width c"
  by sorry

lemma cmin_minimal_strict:
  assumes "c \<in> filter_on_hole h" "c \<noteq> cmin"
  shows "width cmin < width c"              
  by sorry

lemma cmin_max_z_neq_one: "max z cmin < 1"
  by sorry


subsection "Minimum cube on hole is interior"
text "All squares on the boundary of \<^term>\<open>h\<close>"
definition is_on_boundary :: "axis \<Rightarrow> cube \<Rightarrow> bool" where
  "is_on_boundary ax c \<longleftrightarrow> min ax h  = min ax c \<or> max ax h  = max ax c"

text "Shows that IF \<^term>\<open>cmin\<close> is on a boundary \<^term>\<open>ax\<close>, then we find some \<^term>\<open>ax\<close>-coordinate 
\<^term>\<open>r\<close>, which is further from the boundary than the edge of \<^term>\<open>cmin\<close>, but closer than the edge
 of any other cube sufficiently close to the boundary."
lemma cmin_on_boundary:
  assumes "is_on_boundary ax cmin"  "ax \<in> {x, y}"
  shows "\<exists>r . 
    r \<in> (side ax h - (side ax cmin)) \<and> 
    (\<forall> c \<in> filter_on_hole h .  c \<noteq> cmin \<longrightarrow> side ax cmin \<inter> side ax c \<noteq> {} \<longrightarrow> r \<in> side ax c)"
  by sorry

text "Using the previous lemma, we show that \<^term>\<open>cmin\<close> being on the boundary leads to a 
contradiction"
lemma cmin_not_on_boundary_by_axis: 
  assumes "ax \<in> {x, y}"
  shows "\<not>is_on_boundary ax cmin "
  by sorry

text "Previous result, written as inequalities instead"
proposition cmin_not_on_boundary: 
  "min x h < min x cmin \<and> max x cmin < max x h 
        \<and> min y h < min y cmin \<and> max y cmin < max y h"
  by sorry


section "Minimum cube of hole induces hole on top"
text "The main result of this proof - the minimum cube on a hole is itself a hole!"
proposition hole_cmin: 
  shows "is_hole cmin"
  by sorry

text "The main purpose of the previous result: From the proposition, \<^term>\<open>hole_cmin\<close> when given the
hole \<^term>\<open>h\<close> induce another hole \<^term>\<open>h'\<close> (i.e., \<^term>\<open>cmin\<close>), which is in \<^term>\<open>C\<close> and is strictly
smaller."
lemma recursive_step: "\<exists>h'. h' \<in> C \<and> is_hole h' \<and> width h' < width h"
  by sorry
text "Here we end the context in which \<^term>\<open>h\<close> is some fixed hole 
(and hence also the specific \<^term>\<open>cmin\<close>)"
end

section "The main result"
text "We combine the previous lemmas inductively as follows:
  0: Start with the bottom of \<^term>\<open>unit_cube\<close>, which we showed is a hole.
  n: For each hole, take the minimum cube on this hole, which is then a new hole, 
strictly smaller, and in \<^term>\<open>C\<close>. Hence, \<^term>\<open>C\<close> is infinite."
definition next_hole:: "cube \<Rightarrow> cube" where
  "next_hole h = (SOME h' . h' \<in> C \<and> is_hole h' \<and> width h' < width h)"

lemma next_hole_exist: "is_hole h 
  \<Longrightarrow> next_hole h \<in> C \<and> is_hole (next_hole h) \<and> width (next_hole h) < width h"
  by sorry

text "For following proof, we want the image of \<^term>\<open>nth_hole\<close> to be contained in \<^term>\<open>C\<close>, 
hence we start at \<^term>\<open>1\<close> (= \<^term>\<open>Suc 0\<close>). \<^term>\<open>nth_hole\<close> is a function from \<^term>\<open>\<nat>\<close> to \<^term>\<open>C\<close>"
definition nth_hole :: "nat \<Rightarrow> cube" where
  "nth_hole n = (next_hole ^^ Suc n) (shift_down unit_cube)"

text "Each cube in the image of \<^term>\<open>nth_hole\<close> is a hole"
lemma nth_hole_is_hole: "is_hole (nth_hole n)"
  by sorry

text "\<^term>\<open>uminus\<close> is \<^term>\<open>(\<lambda> x. -x)\<close>, and \<^term>\<open>strict_mono\<close> means strictly increasing 
  (not strictly monotonous, as the name might suggest)"
lemma nth_hole_strict_decreasing: "strict_mono (uminus \<circ> width \<circ> nth_hole)"
  by sorry

text "\<^term>\<open>nth_hole\<close> is injective"
lemma nth_hole_inj : "inj nth_hole"
  by sorry

text "The image (range) of \<^term>\<open>nth_hole\<close> is contained in \<^term>\<open>C\<close>"
lemma nth_hole_in: "nth_hole n \<in> C"
  by sorry

text "Same as previous lemma, but written with a quantifier"
lemma nth_hole_in_forall: "\<forall>n . nth_hole n \<in> C"
  by sorry

text "The assumption made in this context (\<^term>\<open>is_dissection C\<close>) leads to \<^term>\<open>False\<close> 
(since \<^term>\<open>nth_hole\<close> generates an infinite subset of \<^term>\<open>C\<close>)"
theorem false_if_dissection: "False"
  by sorry
end \<comment> \<open>Here we end the \<^term>\<open>is_dissection C\<close> context\<close>


text "Main result (spelling out the definition of \<^term>\<open>is_dissection\<close>)."
theorem dissection_does_not_exist:
  "\<nexists> C. (\<forall> c \<in> C. is_valid c) 
  \<and> disjoint (image to_set C) 
  \<and> \<Union>(image to_set C) = to_set unit_cube 
  \<and> inj_on width C 
  \<and> card C \<ge> 2 
  \<and> finite C"
  by sorry
end

