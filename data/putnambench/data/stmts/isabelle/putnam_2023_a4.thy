(*
  Statement-only formalization of PutnamBench artifact putnam_2023_a4,
  concerning density of integer linear combinations of the twelve unit vectors
  pointing to the vertices of a regular icosahedron in real three-space. This
  file contains no proof.
*)

theory putnam_2023_a4
  imports Complex_Main
begin

datatype putnam_2023_a4_vertex =
    V0 | V1 | V2 | V3 | V4 | V5 | V6 | V7 | V8 | V9 | V10 | V11

type_synonym putnam_2023_a4_point = "real \<times> real \<times> real"

definition putnam_2023_a4_phi :: real where
  "putnam_2023_a4_phi = (1 + sqrt 5) / 2"

definition putnam_2023_a4_add ::
    "putnam_2023_a4_point \<Rightarrow> putnam_2023_a4_point \<Rightarrow>
      putnam_2023_a4_point" where
  "putnam_2023_a4_add p q =
    (fst p + fst q,
      fst (snd p) + fst (snd q),
      snd (snd p) + snd (snd q))"

definition putnam_2023_a4_subtract ::
    "putnam_2023_a4_point \<Rightarrow> putnam_2023_a4_point \<Rightarrow>
      putnam_2023_a4_point" where
  "putnam_2023_a4_subtract p q =
    (fst p - fst q,
      fst (snd p) - fst (snd q),
      snd (snd p) - snd (snd q))"

definition putnam_2023_a4_scale ::
    "real \<Rightarrow> putnam_2023_a4_point \<Rightarrow> putnam_2023_a4_point" where
  "putnam_2023_a4_scale c p =
    (c * fst p, c * fst (snd p), c * snd (snd p))"

definition putnam_2023_a4_norm :: "putnam_2023_a4_point \<Rightarrow> real" where
  "putnam_2023_a4_norm p =
    sqrt (fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2)"

fun putnam_2023_a4_raw_vertex ::
    "putnam_2023_a4_vertex \<Rightarrow> putnam_2023_a4_point" where
  "putnam_2023_a4_raw_vertex V0 = (1, putnam_2023_a4_phi, 0)"
| "putnam_2023_a4_raw_vertex V1 = (-1, putnam_2023_a4_phi, 0)"
| "putnam_2023_a4_raw_vertex V2 = (1, -putnam_2023_a4_phi, 0)"
| "putnam_2023_a4_raw_vertex V3 = (-1, -putnam_2023_a4_phi, 0)"
| "putnam_2023_a4_raw_vertex V4 = (putnam_2023_a4_phi, 0, 1)"
| "putnam_2023_a4_raw_vertex V5 = (putnam_2023_a4_phi, 0, -1)"
| "putnam_2023_a4_raw_vertex V6 = (-putnam_2023_a4_phi, 0, 1)"
| "putnam_2023_a4_raw_vertex V7 = (-putnam_2023_a4_phi, 0, -1)"
| "putnam_2023_a4_raw_vertex V8 = (0, 1, putnam_2023_a4_phi)"
| "putnam_2023_a4_raw_vertex V9 = (0, -1, putnam_2023_a4_phi)"
| "putnam_2023_a4_raw_vertex V10 = (0, 1, -putnam_2023_a4_phi)"
| "putnam_2023_a4_raw_vertex V11 = (0, -1, -putnam_2023_a4_phi)"

definition putnam_2023_a4_icosahedron_vertex ::
    "putnam_2023_a4_vertex \<Rightarrow> putnam_2023_a4_point" where
  "putnam_2023_a4_icosahedron_vertex i =
    putnam_2023_a4_scale
      (inverse (sqrt (1 + putnam_2023_a4_phi ^ 2)))
      (putnam_2023_a4_raw_vertex i)"

definition putnam_2023_a4_linear_isometry ::
    "(putnam_2023_a4_point \<Rightarrow> putnam_2023_a4_point) \<Rightarrow> bool" where
  "putnam_2023_a4_linear_isometry g \<longleftrightarrow>
    (\<forall>x y. g (putnam_2023_a4_add x y) =
      putnam_2023_a4_add (g x) (g y)) \<and>
    (\<forall>c x. g (putnam_2023_a4_scale c x) =
      putnam_2023_a4_scale c (g x)) \<and>
    bij g \<and>
    (\<forall>x. putnam_2023_a4_norm (g x) = putnam_2023_a4_norm x)"

definition putnam_2023_a4_integer_combination ::
    "(putnam_2023_a4_vertex \<Rightarrow> int) \<Rightarrow>
      (putnam_2023_a4_vertex \<Rightarrow> putnam_2023_a4_point) \<Rightarrow>
      putnam_2023_a4_point" where
  "putnam_2023_a4_integer_combination a v =
    ((\<Sum>i\<in>UNIV. real_of_int (a i) * fst (v i)),
      (\<Sum>i\<in>UNIV. real_of_int (a i) * fst (snd (v i))),
      (\<Sum>i\<in>UNIV. real_of_int (a i) * snd (snd (v i))))"

theorem putnam_2023_a4:
  fixes v :: "putnam_2023_a4_vertex \<Rightarrow> putnam_2023_a4_point"
    and w :: putnam_2023_a4_point
    and epsilon :: real
  assumes hv:
    "\<exists>g. putnam_2023_a4_linear_isometry g \<and>
      (\<forall>i. g (v i) = putnam_2023_a4_icosahedron_vertex i)"
    and hepsilon: "epsilon > 0"
  shows "\<exists>a :: putnam_2023_a4_vertex \<Rightarrow> int.
    putnam_2023_a4_norm
      (putnam_2023_a4_subtract
        (putnam_2023_a4_integer_combination a v) w) < epsilon"
  sorry

end
