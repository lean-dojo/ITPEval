(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b4, concerning
  the number of regions cut from the unit sphere by great circles in general
  position. This file contains no proof.
*)

theory putnam_1964_b4
  imports Complex_Main
begin

type_synonym putnam_1964_b4_point = "real \<times> real \<times> real"

definition putnam_1964_b4_dot ::
    "putnam_1964_b4_point \<Rightarrow> putnam_1964_b4_point \<Rightarrow> real" where
  "putnam_1964_b4_dot p q =
    fst p * fst q +
    fst (snd p) * fst (snd q) +
    snd (snd p) * snd (snd q)"

definition putnam_1964_b4_sphere :: "putnam_1964_b4_point set" where
  "putnam_1964_b4_sphere =
    {p. putnam_1964_b4_dot p p = 1}"

definition putnam_1964_b4_solution :: "nat \<Rightarrow> nat" where
  "putnam_1964_b4_solution = (\<lambda>n. n ^ 2 - n + 2)"

theorem putnam_1964_b4:
  fixes n :: nat
    and C :: "nat \<Rightarrow> putnam_1964_b4_point set"
    and v :: "nat \<Rightarrow> putnam_1964_b4_point"
    and IsRegion :: "putnam_1964_b4_point set \<Rightarrow> bool"
  assumes hn: "0 < n"
    and hv: "\<forall>i<n. C i =
      putnam_1964_b4_sphere \<inter>
        {x. putnam_1964_b4_dot (v i) x = 0}"
    and hv_nonzero: "\<forall>i<n. v i \<noteq> (0, 0, 0)"
    and hCinj: "\<forall>i<n. \<forall>j<n. C i = C j \<longrightarrow> i = j"
    and hT2: "\<forall>x\<in>putnam_1964_b4_sphere.
      \<forall>y\<in>putnam_1964_b4_sphere.
        card {i :: nat. i < n \<and> {x, y} \<subseteq> C i} \<le> 2"
    and IsRegion_def: "\<forall>R. IsRegion R \<longleftrightarrow>
      R \<noteq> {} \<and>
      (\<exists>sign :: nat \<Rightarrow> real.
        (\<forall>i<n. sign i \<noteq> 0) \<and>
        R = putnam_1964_b4_sphere \<inter>
          {x. \<forall>i<n.
            sgn (putnam_1964_b4_dot (v i) x) = sign i})"
  shows "card {R :: putnam_1964_b4_point set. IsRegion R} =
    putnam_1964_b4_solution n"
  sorry

end
