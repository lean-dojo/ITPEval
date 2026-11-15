theory Pick
imports
  Polygon_Splitting
  Elementary_Triangle_Area
begin

section "Setup"

subsection "Integral Points Cardinality Properties"
lemma bounded_finite:
  fixes A:: "(real^2) set"
  assumes "bounded A"
  shows "finite {x::(real^2). integral_vec x \<and> x \<in> A}" (is "finite ?A_int")
  by sorry

lemma finite_path_image:
  assumes "polygon p"
  shows "finite {x. integral_vec x \<and> x \<in> path_image p}"
  by sorry

lemma finite_path_inside:
  assumes "polygon p"
  shows "finite {x. integral_vec x \<and> x \<in> path_inside p}"
  by sorry

lemma bounded_finite_inside:
  fixes B:: "(real^2) set"
  assumes "simple_path p"
  shows "bounded (path_inside p)"
  by sorry

lemma finite_integral_points_path_image:
  assumes "simple_path p"
  shows "finite {x. integral_vec x \<and> x \<in> path_image p}"
  by sorry

lemma finite_integral_points_path_inside:
  assumes "simple_path p"
  shows "finite {x. integral_vec x \<and> x \<in> path_inside p}"
  by sorry

section "Pick splitting"

lemma pick_split_path_union_main:
  assumes is_split: "is_polygon_split_path vts i j cutvts"
  assumes "vts1 = (take i vts)" 
  assumes "vts2 = (take (j - i - 1) (drop (Suc i) vts))"
  assumes "vts3 = drop (j - i) (drop (Suc i) vts)"
  assumes "x = vts!i"
  assumes "y = vts!j"
  assumes "cutpath = make_polygonal_path (x # cutvts @ [y])"
  assumes p: "p = make_polygonal_path (vts@[vts!0])" (is "p = make_polygonal_path ?p_vts")
  assumes p1: "p1 = make_polygonal_path (x#(vts2 @ [y] @ (rev cutvts) @ [x]))" (is "p1 = make_polygonal_path ?p1_vts")
  assumes p2: "p2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [vts ! 0])" (is "p2 = make_polygonal_path ?p2_vts")
  assumes I1: "I1 = card {x. integral_vec x \<and> x \<in> path_inside p1}" 
  assumes B1: "B1 = card {x. integral_vec x \<and> x \<in> path_image p1}"
  assumes I2: "I2 = card {x. integral_vec x \<and> x \<in> path_inside p2}" 
  assumes B2: "B2 = card {x. integral_vec x \<and> x \<in> path_image p2}"
  assumes I: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes all_integral_vts: "all_integral vts"
  shows "measure lebesgue (path_inside p1) = I1 + B1/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p) = I + B/2 - 1"
        "measure lebesgue (path_inside p) = I + B/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
        "measure lebesgue (path_inside p) = I + B/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p1) = I1 + B1/2 - 1
          \<Longrightarrow> measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
  by sorry

lemma pick_split_union:
  assumes is_split: "is_polygon_split vts i j"
  assumes "vts1 = (take i vts)" 
  assumes "vts2 = (take (j - i - 1) (drop (Suc i) vts)) "
  assumes "vts3 = drop (j - i) (drop (Suc i) vts) "
  assumes "x = vts ! i "
  assumes "y = vts ! j "
  assumes p: "p = make_polygonal_path (vts@[vts!0])" (is "p = make_polygonal_path ?p_vts")
  assumes p1: "p1 = make_polygonal_path (x#(vts2@[y, x]))" (is "p1 = make_polygonal_path ?p1_vts")
  assumes p2: "p2 = make_polygonal_path (vts1 @ [x, y] @ vts3 @ [vts ! 0])" (is "p2 = make_polygonal_path ?p2_vts")
  assumes I1: "I1 = card {x. integral_vec x \<and> x \<in> path_inside p1}" 
  assumes B1: "B1 = card {x. integral_vec x \<and> x \<in> path_image p1}"
  assumes pick1: "measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
  assumes I2: "I2 = card {x. integral_vec x \<and> x \<in> path_inside p2}" 
  assumes B2: "B2 = card {x. integral_vec x \<and> x \<in> path_image p2}"
  assumes pick2: "measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
  assumes I: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes all_integral_vts: "all_integral vts"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
        "measure lebesgue (path_inside p) = measure lebesgue (path_inside p1) + measure lebesgue (path_inside p2)"
  by sorry

lemma pick_split_path_union:
  assumes is_split: "is_polygon_split_path vts i j cutvts"
  assumes "vts1 = (take i vts)" 
  assumes "vts2 = (take (j - i - 1) (drop (Suc i) vts))"
  assumes "vts3 = drop (j - i) (drop (Suc i) vts)"
  assumes "x = vts!i"
  assumes "y = vts!j"
  assumes "cutpath = make_polygonal_path (x # cutvts @ [y])"
  assumes p: "p = make_polygonal_path (vts@[vts!0])" (is "p = make_polygonal_path ?p_vts")
  assumes p1: "p1 = make_polygonal_path (x#(vts2 @ [y] @ (rev cutvts) @ [x]))" (is "p1 = make_polygonal_path ?p1_vts")
  assumes p2: "p2 = make_polygonal_path (vts1 @ ([x] @ cutvts @ [y]) @ vts3 @ [vts ! 0])" (is "p2 = make_polygonal_path ?p2_vts")
  assumes I1: "I1 = card {x. integral_vec x \<and> x \<in> path_inside p1}" 
  assumes B1: "B1 = card {x. integral_vec x \<and> x \<in> path_image p1}"
  assumes pick1: "measure lebesgue (path_inside p1) = I1 + B1/2 - 1"
  assumes I2: "I2 = card {x. integral_vec x \<and> x \<in> path_inside p2}" 
  assumes B2: "B2 = card {x. integral_vec x \<and> x \<in> path_image p2}"
  assumes pick2: "measure lebesgue (path_inside p2) = I2 + B2/2 - 1"
  assumes I: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes all_integral_vts: "all_integral vts"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

lemma pick_triangle_basic_split:
  assumes "p = make_triangle a b c" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}" and
          d_prop: "d \<in> path_image (linepath a b) \<and> d \<notin> {a, b, c}"
  shows "good_linepath c d [a, d, b, c, a]
          \<and> path_image (make_polygonal_path [a, d, b, c, a]) = path_image p"
  by sorry

section "Convex Hull Has Good Linepath"

lemma leq_2_extreme_points_means_collinear:
  fixes vts :: "'a::euclidean_space set"
  assumes "finite vts"
  assumes "card {v. v extreme_point_of (convex hull vts)} \<le> 2"
  shows "collinear vts"
  by sorry

lemma convex_hull_non_extreme_point_in_open_seg:
  assumes "H = convex hull vts"
  assumes "x \<in> H - {v. v extreme_point_of H}"
  shows "\<exists>a b. a \<in> H \<and> b \<in> H \<and> x \<in> open_segment a b"
  by sorry

lemma convex_hull_extreme_points_vertex_split:
  fixes vts :: "(real^2) set"
  assumes "H = convex hull vts"
  assumes "finite vts"
  assumes "card {v. v extreme_point_of H} \<ge> 4"
  assumes "{a, b, c} \<subseteq> {v. v extreme_point_of H} \<and> distinct [a, b, c]"
  shows "path_image (linepath a b) \<inter> interior H \<noteq> {}
      \<or> path_image (linepath b c) \<inter> interior H \<noteq> {}
      \<or> path_image (linepath c a) \<inter> interior H \<noteq> {}"
  by sorry

lemma convex_hull_has_vertex_split_helper_wlog:
  assumes "p = make_triangle a b c" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}" and
    d_prop: "d \<in> path_image (linepath a b) \<and> d \<notin> {a, b, c}"
  shows "path_image (linepath c d) \<inter> path_inside p \<noteq> {}"
  by sorry

lemma convex_hull_has_vertex_split_helper:
  assumes "p = make_triangle a b c" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}" and
    d_prop: "d \<in> path_image p \<and> d \<notin> {a, b, c}"
  shows "\<exists>x y. {x, y} \<subseteq> {a, b, c, d} \<and> x \<noteq> y \<and> path_image (linepath x y) \<inter> path_inside p \<noteq> {}"
  by sorry

lemma convex_hull_has_vertex_split:
  fixes vts :: "(real^2) set"
  assumes "H = convex hull vts"
  assumes "\<not> collinear vts"
  assumes "card vts > 3"
  assumes "finite vts"
  shows "\<exists>a b. {a, b} \<subseteq> vts \<and> a \<noteq> b \<and> path_image (linepath a b) \<inter> interior H \<noteq> {}"
  by sorry

lemma convex_polygon_has_good_linepath_helper:
  assumes "polygon_of p vts"
  assumes "convex (path_inside p \<union> path_image p)"
  assumes "card (set vts) > 3"
  obtains a b where "{a, b} \<subseteq> set vts \<and> a \<noteq> b \<and> \<not> path_image (linepath a b) \<subseteq> path_image p"
  by sorry

lemma convex_polygon_has_good_linepath:
  assumes "convex (path_inside p \<union> path_image p)"
  assumes "polygon p"
  assumes "p = make_polygonal_path vts"
  assumes "card (set vts) > 3"
  shows "\<exists>a b. good_linepath a b vts"
  by sorry

section "Pick's Theorem"

definition integral_inside:
  "integral_inside p = {x. integral_vec x \<and> x \<in> path_inside p}"

definition integral_boundary:
  "integral_boundary p = {x. integral_vec x \<and> x \<in> path_image p}"

subsection "Pick's Theorem Triangle Case"

definition pick_triangle:
  "pick_triangle p a b c \<longleftrightarrow>
      p = make_triangle a b c
      \<and> all_integral [a, b, c]
      \<and> distinct [a, b, c]
      \<and> \<not> collinear {a, b, c}"

definition pick_holds:
  "pick_holds p \<longleftrightarrow>
    (let I = card {x. integral_vec x \<and> x \<in> path_inside p} in
    let B = card {x. integral_vec x \<and> x \<in> path_image p} in
      measure lebesgue (path_inside p) = I + B/2 - 1)"

lemma pick_triangle_wlog_helper:
  assumes "pick_triangle p a b c" and
          "I = card (integral_inside p)" and
          "B = card (integral_boundary p)" and
          "integral_inside p = {}" and
          "integral_vec d \<and> d \<in> path_image (linepath a b) \<and> d \<notin> {a, b, c}" and "d \<notin> {a, b, c}" and
          ih: "\<And>p' a' b' c'. (card (integral_inside p') + card (integral_boundary p') < I + B) \<Longrightarrow> pick_triangle p' a' b' c' \<Longrightarrow> pick_holds p'"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

lemma pick_triangle_helper:
  assumes "pick_triangle p a b c" and
          "I = card (integral_inside p)" and
          "B = card (integral_boundary p)" and
          "integral_inside p = {}" and
          "integral_vec d \<and> d \<notin> {a, b, c}" and "d \<notin> {a, b, c}" and
          "d \<in> path_image (linepath a b)
            \<or> d \<in> path_image (linepath b c)
            \<or> d \<in> path_image (linepath c a)" and
          ih: "\<And>p' a' b' c'. (card (integral_inside p') + card (integral_boundary p') < I + B) \<Longrightarrow> pick_triangle p' a' b' c' \<Longrightarrow> pick_holds p'"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

lemma triangle_3_split_helper:
  fixes a b :: "'a::euclidean_space"
  assumes "a \<in> frontier S"
  assumes "b \<in> interior S"
  assumes "convex S"
  assumes "closed S"
  shows "path_image (linepath a b) \<inter> frontier S = {a}"
  by sorry

lemma unit_triangle_interior_point_not_collinear_e1_e2:
  assumes "p = make_triangle (vector [0, 0]) (vector [1, 0]) (vector [0, 1])"
    (is "p = make_triangle ?O ?e1 ?e2")
  assumes "z \<in> path_inside p"
  shows "\<not> collinear {?O, ?e1, z}"
  by sorry

lemma triangle_interior_point_not_collinear_vertices_wlog_helper:
  assumes "p = make_triangle a b c"
  assumes "polygon p"
  assumes "z \<in> path_inside p"
  shows "\<not> collinear {a, b, z}"
  by sorry

lemma triangle_interior_point_not_collinear_vertices:
  assumes "p = make_triangle a b c"
  assumes "polygon p"
  assumes "z \<in> path_inside p"
  shows "\<not> collinear {a, b, z} \<and> \<not> collinear {a, c, z} \<and> \<not> collinear {b, c, z}"
  by sorry


lemma triangle_3_split:
  assumes "p = make_triangle a b c"
  assumes "polygon p"
  assumes "z \<in> path_inside p"
  shows "is_polygon_split_path [a, b, c] 0 1 [z]"
        "is_polygon_split [a, z, b, c] 1 3"
        "a \<notin> path_image (make_triangle z b c) \<union> path_inside (make_triangle z b c)"
        "b \<notin> path_image (make_triangle a z c) \<union> path_inside (make_triangle a z c)"
        "c \<notin> path_image (make_triangle a b z) \<union> path_inside (make_triangle a b z)"
  by sorry

lemma smaller_triangle:
  assumes "\<not> collinear {a, b, c} \<and> \<not> collinear {a', b', c'}"
  assumes "p = make_triangle a b c"
  assumes "p' = make_triangle a' b' c'"
  assumes "path_inside p \<subseteq> path_inside p'"
  assumes "\<exists>d. integral_vec d \<and> d \<in> path_image p' \<union> path_inside p' \<and> d \<notin> path_image p \<union> path_inside p"
  shows "card (integral_inside p) + card (integral_boundary p) < card (integral_inside p') + card (integral_boundary p')"
  by sorry

lemma pick_elem_triangle:
  fixes p :: "R_to_R2"
  assumes p_triangle: "p = make_triangle a b c"
  assumes elem_triangle: "elem_triangle a b c" 
  assumes "I = card {x. integral_vec x \<and> x \<in> path_inside p}" and
          "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

lemma pick_triangle_lemma:
  fixes p :: "R_to_R2"
  assumes "p = make_triangle a b c" and "all_integral [a, b, c]" and "distinct [a, b, c]" and "\<not> collinear {a, b, c}"
          "I = card {x. integral_vec x \<and> x \<in> path_inside p}" and
          "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

subsection "Pocket properties"

definition index_not_in_set :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> bool"
  where "index_not_in_set vts A i \<longleftrightarrow> i \<in> {i. i < length vts \<and> vts ! i \<notin> A}"

definition min_index_not_in_set:: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat"
  where "min_index_not_in_set vts A = (LEAST i. index_not_in_set vts A i)"

definition nonzero_index_in_set :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "nonzero_index_in_set vts A i \<longleftrightarrow> i \<in> {i. 0 < i \<and> i < length vts \<and> vts ! i \<in> A}"

definition min_nonzero_index_in_set :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> nat" where
  "min_nonzero_index_in_set vts A = (LEAST i. nonzero_index_in_set vts A i)"

(* NOTE: Requires rotation: enforce that vts!0 is in convex_hull_vts,
  since the pocket can "loop around" the end of the polygon vts list
*)
definition construct_pocket_0 :: "(real^2) list \<Rightarrow> (real^2) set \<Rightarrow> (real^2) list" where
  "construct_pocket_0 vts A = take ((min_nonzero_index_in_set vts A) + 1) vts"

definition is_pocket_0 :: "(real^2) list \<Rightarrow> (real^2) list \<Rightarrow> bool" where
  "is_pocket_0 vts vts' \<longleftrightarrow>
      polygon (make_polygonal_path vts)
      \<and> (\<exists>i. vts' = take i vts)
      \<and> 3 \<le> length vts' \<and> length vts' < length vts
      \<and> hd vts' \<in> frontier (convex hull (set vts)) \<and> last vts' \<in> frontier (convex hull (set vts))
      \<and> set (tl (butlast vts')) \<subseteq> interior (convex hull (set vts))"

(* i is the length of the pocket path *)
definition fill_pocket_0 :: "(real^2) list \<Rightarrow> nat \<Rightarrow> (real^2) list" where
  "fill_pocket_0 vts i = (hd vts) # (drop (i-1) vts)"

lemma min_nonzero_index_in_set_exists:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  shows "\<exists>i. nonzero_index_in_set vts A i"
  by sorry

lemma min_nonzero_index_in_set_defined:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  defines "i \<equiv> min_nonzero_index_in_set vts A"
  shows "nonzero_index_in_set vts A i \<and> (\<forall>j < i. \<not> nonzero_index_in_set vts A j)"
  by sorry

lemma min_index_not_in_set_exists:
  assumes "set vts \<supset> A"
  shows "\<exists>i. index_not_in_set vts A i"
  by sorry

lemma min_index_not_in_set_defined:
  assumes "set vts \<supset> A"
  defines "i \<equiv> min_index_not_in_set vts A"
  shows "index_not_in_set vts A i \<and> (\<forall>j < i. \<not> index_not_in_set vts A j)"
  by sorry

lemma min_nonzero_index_in_set_bound:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  shows "min_nonzero_index_in_set vts A < length vts"
  by sorry

lemma construct_pocket_0_subset_vts:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  shows "set (construct_pocket_0 vts A) \<subseteq> set vts"
  by sorry

lemma min_index_not_in_set_0:
  assumes "set vts \<supset> A"
  assumes "vts!0 \<in> A"
  defines "i \<equiv> min_index_not_in_set vts A"
  defines "r \<equiv> i - 1"
  shows "vts!r \<in> A"
  by sorry

lemma construct_pocket_0_last_in_set:
  assumes "set (tl vts) \<inter> A \<noteq> {}"
  assumes "vts!0 \<in> A"
  defines "p \<equiv> construct_pocket_0 vts A"
  shows "last p \<in> A"
  by sorry

lemma construct_pocket_0_first_last_distinct:
  assumes "card A \<ge> 2"
  assumes "A \<subseteq> set vts"
  assumes "distinct (butlast vts)"
  assumes "hd vts = last vts"
  shows "hd (construct_pocket_0 vts A) \<noteq> last (construct_pocket_0 vts A)"
  by sorry

lemma construct_pocket_is_pocket:
  assumes "polygon (make_polygonal_path vts)"
  assumes "vts!0 \<in> frontier (convex hull (set vts))"
  assumes "vts!1 \<notin> frontier (convex hull (set vts))"
  shows "is_pocket_0 vts (construct_pocket_0 vts (set vts \<inter> frontier (convex hull (set vts))))"
  by sorry


lemma exists_point_above_interior:
  fixes a :: "real^2"
  assumes "a \<in> interior (convex hull S)"
  obtains x where "x \<in> S \<and> x$2 > a$2"
  by sorry

lemma exists_point_above_convex_hull_interior:
  fixes S :: "(real^2) set"
  assumes "S \<noteq> {}"
  assumes "compact S"
  obtains x where "x \<in> S - (interior (convex hull S)) \<and> (\<forall>y \<in> interior (convex hull S). x$2 > y$2)"
  by sorry

lemma flip_function:
  defines "M \<equiv> (vector [vector [1, 0], vector [0, -1]])::(real^2^2)"
  defines "f \<equiv> \<lambda>v. M *v v"
  defines "g \<equiv> (\<lambda>v. vector [v$1, -v$2])::(real^2 \<Rightarrow> real^2)"
  shows "inj f" "f = g"
  by sorry

lemma exists_point_below_convex_hull_interior:
  fixes S :: "(real^2) set"
  assumes "S \<noteq> {}"
  assumes "compact S"
  obtains x where "x \<in> S - (interior (convex hull S)) \<and> (\<forall>y \<in> interior (convex hull S). x$2 < y$2)"
  by sorry

lemma exists_point_above_all:
  fixes p q :: "R_to_R2"
  defines "H \<equiv> convex hull (path_image p \<union> path_image q)"
  assumes "path p \<and> path q"
  assumes "p`{0<..<1} \<subseteq> interior H"
  assumes "(p 0)$2 = 0 \<and> (p 1)$2 = 0"
  assumes "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0"
  obtains x where "x \<in> path_image q \<and> (\<forall>y \<in> path_image p. x$2 > y$2)"
  by sorry

lemma exists_point_below_all:
  fixes p q :: "R_to_R2"
  defines "H \<equiv> convex hull (path_image p \<union> path_image q)"
  assumes "path p \<and> path q"
  assumes "p`{0<..<1} \<subseteq> interior H"
  assumes "(p 0)$2 = 0 \<and> (p 1)$2 = 0"
  assumes "\<exists>x \<in> path_image p \<union> path_image q. x$2 < 0"
  obtains x where "x \<in> path_image q \<and> (\<forall>y \<in> path_image p. x$2 < y$2)"
  by sorry

lemma pocket_fill_line_int_aux:
  fixes x y z :: "real^2"
  defines "a \<equiv> y$1"
  assumes "x = 0"
  assumes "a > 0 \<and> y$2 = 0"
  assumes "z$1 < 0 \<or> z$1 > a"
  assumes "z$2 = 0"
  assumes "convex A \<and> compact A"
  assumes "{x, y, z} \<subseteq> A"
  assumes "{x, y} \<subseteq> frontier A"
  shows "z \<in> frontier A \<and> closed_segment x y \<subseteq> frontier A"
  by sorry

lemma axis_dist:
  fixes a b :: "real^2"
  shows "a$2 = b$2 \<Longrightarrow> dist a b = dist (a$1) (b$1)" "a$1 = b$1 \<Longrightarrow> dist a b = dist (a$2) (b$2)"
  by sorry

lemma dist_bound_1:
  fixes a b x :: "real^2"
  assumes "a$2 = x$2"
  assumes "b \<in> ball x \<epsilon>"
  assumes "\<epsilon> < dist a x"
  shows "a$1 < x$1 \<Longrightarrow> b$1 > a$1" "a$1 > x$1 \<Longrightarrow> b$1 < a$1"
  by sorry

lemma dist_bound_2:
  fixes a b x :: "real^2"
  assumes "a$1 = x$1"
  assumes "b \<in> ball x \<epsilon>"
  assumes "\<epsilon> < dist a x"
  shows "a$2 < x$2 \<Longrightarrow> b$2 > a$2" "a$2 > x$2 \<Longrightarrow> b$2 < a$2"
  by sorry

lemma linepath_bound_1:
  fixes x y :: "real^2"
  shows "a < x$1 \<and> a < y$1 \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). a < v$1"
        "x$1 < b \<and> y$1 < b \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). v$1 < b"
  by sorry

lemma linepath_bound_2:
  fixes x y :: "real^2"
  shows "a < x$2 \<and> a < y$2 \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). a < v$2"
        "x$2 < b \<and> y$2 < b \<Longrightarrow> \<forall>v \<in> path_image (linepath x y). v$2 < b"
  by sorry

lemma linepath_int_corner:
  fixes x y z :: "real^2"
  assumes "x$2 \<noteq> y$2"
  assumes "y$2 = z$2"
  shows "path_image (linepath x y) \<inter> path_image (linepath y z) = {y}"
    (is "path_image ?l1 \<inter> path_image ?l2 = {y}")
  by sorry

lemma linepath_int_vertical:
  fixes w x y z :: "real^2"
  assumes "w$1 \<noteq> y$1"
  assumes "w$1 = x$1"
  assumes "y$1 = z$1"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
  by sorry

lemma linepath_int_horizontal:
  fixes w x y z :: "real^2"
  assumes "w$2 \<noteq> y$2"
  assumes "w$2 = x$2"
  assumes "y$2 = z$2"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
  by sorry

lemma linepath_int_columns:
  fixes w x y z :: "real^2"
  assumes "w$1 < y$1 \<and> w$1 < z$1"
  assumes "x$1 < y$1 \<and> x$1 < z$1"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
    (is "path_image ?l1 \<inter> path_image ?l2 = {}")
  by sorry

lemma linepath_int_rows:
  fixes w x y z :: "real^2"
  assumes "w$2 < y$2 \<and> w$2 < z$2"
  assumes "x$2 < y$2 \<and> x$2 < z$2"
  shows "path_image (linepath w x) \<inter> path_image (linepath y z) = {}"
    (is "path_image ?l1 \<inter> path_image ?l2 = {}")
  by sorry

lemma horizontal_segment_at_0:
  assumes "a > 0"
  shows "closed_segment ((vector [0, 0])::(real^2)) (vector [a, 0]) = {x. x$2 = 0 \<and> x$1 \<in> {0..a}}"
    (is "?l = ?s")
  by sorry

lemma horizontal_segment_at_0':
  fixes x y :: "real^2"
  assumes "a > 0"
  assumes "x$1 = 0 \<and> x$2 = 0 \<and> y$1 = a \<and> y$2 = 0"
  shows "closed_segment x y = {x. x$2 = 0 \<and> x$1 \<in> {0..a}}"
  by sorry

lemma pocket_fill_line_int_aux1:
  fixes p q :: "R_to_R2"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "path_image q \<inter> {x. x$2 = 0} \<subseteq> l"
  assumes "path_image p \<inter> {x. x$2 = 0} \<subseteq> l"
  assumes "\<forall>v \<in> path_image p. q0$2 \<le> v$2"
  assumes "\<forall>v \<in> path_image p. q1$2 > v$2"
  shows "path_image p \<inter> path_image q \<noteq> {}"
  by sorry

lemma pocket_fill_line_int_aux2:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "convex A \<and> compact A"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p ` {0<..<1} \<subseteq> interior A"
  shows "path_image p \<inter> {x. x$2 = 0} \<subseteq> l"
  by sorry

lemma three_points_on_line:
  fixes a b :: "'a::real_vector"
  assumes "A = affine hull {a, b}"
  assumes "a \<noteq> b"
  assumes "{x, y, z} \<subseteq> A"
  assumes "x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z"
  shows "x \<in> open_segment y z \<or> y \<in> open_segment x z \<or> z \<in> open_segment x y"
  by sorry

lemma pocket_fill_line_int_aux3:
  fixes A :: "(real^2) set"
  assumes "convex A \<and> compact A"
  assumes "v \<noteq> 0"
  assumes "closed_segment 0 w \<subseteq> frontier A" (is "closed_segment ?a ?b \<subseteq> _")
  assumes "w \<bullet> v = 0"
  assumes "w \<noteq> 0"
  shows "(A \<subseteq> {x. x \<bullet> v \<le> 0} \<or> A \<subseteq> {x. x \<bullet> v \<ge> 0})" (is "A \<subseteq> ?P1 \<or> A \<subseteq> ?P2")
  by sorry

lemma pocket_fill_line_int_aux4:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "\<forall>v \<in> path_image p. q0$2 \<le> v$2"
  assumes "\<forall>v \<in> path_image p. q1$2 > v$2"
  assumes "convex A \<and> compact A"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image q \<subseteq> A"
  shows "l \<subseteq> frontier A" "\<forall>x \<in> (path_image p) \<union> (path_image q). x$2 \<ge> 0" "q0$2 = 0"
  by sorry

(* slight generalization of aux4*)
lemma pocket_fill_line_int_aux5:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> closed_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {q0, q1}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "A = convex hull (path_image p \<union> path_image q)"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image q \<subseteq> A"
  assumes "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0" (* wlog; if not the case, we flip across x axis *)
  assumes "q0 = p1 \<and> q1 = p0"
  shows "l \<subseteq> frontier A" "\<forall>x \<in> path_image p \<union> path_image q. x$2 \<ge> 0"
  by sorry

lemma pocket_fill_line_int_aux6:
  fixes p q :: "R_to_R2"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "p0 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "q0$1 \<in> {0..a} \<and> q0$2 = 0"
  assumes "\<forall>x \<in> path_image p. q1$2 > x$2"
  assumes "\<forall>x \<in> path_image p \<union> path_image q. x$2 \<ge> 0"
  shows "path_image p \<inter> path_image q \<noteq> {}"
  by sorry

lemma pocket_fill_line_int_aux7:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> open_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {q0, q1}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "A = convex hull (path_image p \<union> path_image q)"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "\<exists>x \<in> p`{0<..<1}. x$2 \<ge> 0" (* wlog; if not the case, we flip across x axis *)
  assumes "q0 = p1 \<and> q1 = p0"
  shows "path_image q \<inter> l = {}" "closed_segment p0 p1 \<subseteq> frontier A"
  by sorry

(* could not find in libraries, seems like it should be there *)
lemma frontier_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "inj f"
  shows "f ` (frontier S) = frontier (f ` S)"
  by sorry

lemma pocket_fill_line_int_aux8:
  fixes p q :: "R_to_R2"
  fixes A :: "(real^2) set"
  defines "p0 \<equiv> pathstart p"
  defines "p1 \<equiv> pathfinish p"
  defines "q0 \<equiv> pathstart q"
  defines "q1 \<equiv> pathfinish q"
  defines "a \<equiv> p1$1"
  defines "l \<equiv> open_segment p0 p1"
  assumes "simple_path p"
  assumes "simple_path q"
  assumes "path_image p \<inter> path_image q = {q0, q1}"
  assumes "p0$1 = 0 \<and> p0$2 = 0 \<and> p1$2 = 0"
  assumes "a > 0"
  assumes "A = convex hull (path_image p \<union> path_image q)"
  assumes "{p0, p1} \<subseteq> frontier A"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "q0 = p1 \<and> q1 = p0"
  shows "path_image q \<inter> l = {} \<and> l \<subseteq> frontier A"
  by sorry

lemma simple_path_linear_image:
  assumes "simple_path p"
  assumes "inj f \<and> bounded_linear f"
  shows "simple_path (f \<circ> p)" 
  by sorry

lemma vts_interior:
  fixes vts
  defines "p \<equiv> make_polygonal_path vts"
  assumes "convex H"
  assumes "\<forall>j \<in> {0<..<length vts - 1}. vts!j \<notin> frontier H"
  assumes "loop_free p"
  assumes "path_image p \<subseteq> H"
  assumes "length vts \<ge> 3"
  shows "p`{0<..<1} \<subseteq> interior H"
  by sorry

lemma pocket_fill_line_int_0:
  assumes "polygon_of r vts"
  defines "H \<equiv> convex hull (set vts)"
  assumes "2 \<le> i \<and> i < length vts - 1"
  defines "a \<equiv> hd vts"
  defines "b \<equiv> vts!i"
  assumes "{a, b} \<subseteq> frontier H"
  assumes "\<forall>j \<in> {0<..<i}. vts!j \<notin> frontier H"
  assumes "a = 0"
  shows "path_image (linepath a b) \<inter> path_image r = {a, b}"
        "path_image (linepath a b) \<subseteq> frontier H"
  by sorry

lemma linepath_translation: "(\<lambda>v. v - a) \<circ> (linepath x y) = linepath ((\<lambda>v. v - a) x) ((\<lambda>v. v - a) y)"
  by sorry

lemma linepath_image_translation:
    "path_image ((\<lambda>v. v - a) \<circ> (linepath x y)) = path_image (linepath ((\<lambda>v. v - a) x) ((\<lambda>v. v - a) y))"
  by sorry

lemma make_polygonal_path_translate:
  assumes "length vts \<ge> 1"
  shows "(\<lambda>v. v - a) \<circ> (make_polygonal_path vts) = make_polygonal_path (map (\<lambda>v. v - a) vts)"
  by sorry

lemma pocket_fill_line_int:
  assumes "polygon_of r vts"
  defines "H \<equiv> convex hull (set vts)"
  assumes "2 \<le> i \<and> i < length vts - 1"
  defines "a \<equiv> hd vts"
  defines "b \<equiv> vts!i"
  assumes "{a, b} \<subseteq> frontier H"
  assumes "\<forall>j \<in> {0<..<i}. vts!j \<notin> frontier H"
  shows "path_image (linepath a b) \<inter> path_image r = {a, b}"
        "path_image (linepath a b) \<subseteq> frontier H"
  by sorry

(* not in libraries; would be nice? *)
lemma path_connected_simple_path_endless:
  assumes "simple_path p"
  shows "path_connected (path_image p - {pathstart p, pathfinish p})" (is "path_connected ?S")
  by sorry

lemma simple_loop_split:
  assumes "simple_path p \<and> closed_path p"
  assumes "simple_path q"
  assumes "path_image q \<inter> path_image p = {q 0, q 1}"
  assumes "path_image q \<inter> path_inside p \<noteq> {}"
  shows "q`{0<..<1} \<subseteq> path_inside p"
  by sorry

lemma pocket_path_interior_aux:
  assumes "simple_path p \<and> simple_path q"
  assumes "arc p \<and> arc q"
  assumes "q 0 = p 1 \<and> q 1 = p 0"
  assumes "path_image p \<inter> path_image q = {p 0, q 0}"
  defines "A \<equiv> convex hull (path_image p \<union> path_image q)"
  defines "l \<equiv> linepath (p 0) (p 1)"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image l \<subseteq> frontier A"
  assumes "path_image q \<inter> path_image l = {l 0, q 0}"
  shows "p`{0<..<1} \<inter> path_inside (l +++ q) \<noteq> {}"
        "simple_path (l +++ q) \<and> closed_path (l +++ q)"
        "path_image p \<inter> path_image (l +++ q) = {p 0, p 1}"
  by sorry

lemma pocket_path_interior:
  assumes "simple_path p \<and> simple_path q"
  assumes "arc p \<and> arc q"
  assumes "q 0 = p 1 \<and> q 1 = p 0"
  assumes "path_image p \<inter> path_image q = {p 0, q 0}"
  defines "A \<equiv> convex hull (path_image p \<union> path_image q)"
  defines "l \<equiv> linepath (p 0) (p 1)"
  assumes "p`{0<..<1} \<subseteq> interior A"
  assumes "path_image l \<subseteq> frontier A"
  assumes "path_image q \<inter> path_image l = {l 0, q 0}"
  shows "p`{0<..<1} \<subseteq> path_inside (l +++ q)"
  by sorry

lemma pocket_path_good:
  assumes "polygon (make_polygonal_path vts)"
  assumes "vts!0 \<in> frontier (convex hull (set vts))"
  assumes "vts!1 \<notin> frontier (convex hull (set vts))"
  assumes "\<not> convex (path_image (make_polygonal_path vts) \<union> path_inside (make_polygonal_path vts))"
  defines "pocket_path_vts \<equiv> construct_pocket_0 vts (set vts \<inter> frontier (convex hull (set vts)))"
  defines "pocket \<equiv> make_polygonal_path (pocket_path_vts @ [pocket_path_vts!0])"
  defines "filled_vts \<equiv> fill_pocket_0 vts (length pocket_path_vts)"
  defines "filled_p \<equiv> make_polygonal_path filled_vts"
  defines "a \<equiv> hd pocket_path_vts"
  defines "b \<equiv> last pocket_path_vts"
  defines "good_pocket_path_vts \<equiv> tl (butlast pocket_path_vts)"
  shows "polygon filled_p"
        "is_polygon_split_path (butlast filled_vts) 0 1 good_pocket_path_vts"
        "polygon pocket"
        "card (set pocket_path_vts) < card (set vts)"
        "card (set filled_vts) < card (set vts)"
  by sorry

subsection "Arbitrary Polygon Case"

lemma pick_rotate:
  assumes "polygon_of p vts"
  assumes "all_integral vts"
  obtains p' vts' where "polygon_of p' vts'
    \<and> vts'!0 \<in> frontier (convex hull (set vts'))
    \<and> path_image p' = path_image p
    \<and> all_integral vts'
    \<and> set vts' = set vts"
  by sorry

lemma pick_unrotated:
  fixes p :: "R_to_R2"
  assumes polygon: "polygon p"
  assumes polygonal_path: "p = make_polygonal_path vts"
  assumes int_vertices: "all_integral vts"
  assumes I_is: "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes B_is: "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  assumes "vts!0 \<in> frontier (convex hull (set vts))"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

theorem pick:
  fixes p :: "R_to_R2"
  assumes "polygon p"
  assumes "p = make_polygonal_path vts"
  assumes "all_integral vts"
  assumes "I = card {x. integral_vec x \<and> x \<in> path_inside p}" 
  assumes "B = card {x. integral_vec x \<and> x \<in> path_image p}"
  shows "measure lebesgue (path_inside p) = I + B/2 - 1"
  by sorry

end
