(*
  Statement-only formalization of Hundred Theorems artifact 050,
  "The Number of Platonic Solids". It characterizes the possible uniform
  face-edge and vertex-edge incidence counts of full-dimensional polytopes
  in real three-dimensional space. Real three-space is represented by triples
  of real numbers, with the standard point-set definitions of convex hull,
  supporting face, and affine dimension given below. This file contains no
  proof.
*)

theory Number_of_Platonic_Solids
  imports Complex_Main
begin

type_synonym point3 = "real \<times> (real \<times> real)"

definition lincomb3 ::
    "(point3 \<Rightarrow> real) \<Rightarrow> point3 set \<Rightarrow> point3" where
  "lincomb3 a A =
     ((\<Sum>x\<in>A. a x * fst x),
      ((\<Sum>x\<in>A. a x * fst (snd x)),
       (\<Sum>x\<in>A. a x * snd (snd x))))"

definition affine_independent3 :: "point3 set \<Rightarrow> bool" where
  "affine_independent3 A \<longleftrightarrow>
     finite A \<and>
     (\<forall>a :: point3 \<Rightarrow> real.
        (\<Sum>x\<in>A. a x) = 0 \<and>
        lincomb3 a A = (0, (0, 0))
        \<longrightarrow> (\<forall>x\<in>A. a x = 0))"

definition convex_hull3 :: "point3 set \<Rightarrow> point3 set" where
  "convex_hull3 S =
     {x. \<exists>A :: point3 set. \<exists>a :: point3 \<Rightarrow> real.
        finite A \<and>
        A \<subseteq> S \<and>
        (\<forall>y\<in>A. 0 \<le> a y) \<and>
        (\<Sum>y\<in>A. a y) = 1 \<and>
        x = lincomb3 a A}"

definition polytope3 :: "point3 set \<Rightarrow> bool" where
  "polytope3 p \<longleftrightarrow>
     (\<exists>V :: point3 set. finite V \<and> p = convex_hull3 V)"

definition dot3 :: "point3 \<Rightarrow> point3 \<Rightarrow> real" where
  "dot3 a x =
     fst a * fst x +
     fst (snd a) * fst (snd x) +
     snd (snd a) * snd (snd x)"

definition face_of3 :: "point3 set \<Rightarrow> point3 set \<Rightarrow> bool" where
  "face_of3 f p \<longleftrightarrow>
     (\<exists>a :: point3. \<exists>b :: real.
        f = {x \<in> p. dot3 a x = b} \<and>
        (\<forall>x\<in>p. dot3 a x \<le> b))"

definition has_aff_dim3 :: "point3 set \<Rightarrow> nat \<Rightarrow> bool" where
  "has_aff_dim3 S d \<longleftrightarrow>
     (\<exists>A :: point3 set.
        A \<subseteq> S \<and>
        affine_independent3 A \<and>
        card A = d + 1 \<and>
        (\<forall>B :: point3 set.
           B \<subseteq> S \<and> affine_independent3 B
           \<longrightarrow> card B \<le> d + 1))"

theorem platonic_solids:
  fixes m n :: nat
  shows
    "(\<exists>p :: point3 set.
       polytope3 p \<and>
       has_aff_dim3 p 3 \<and>
       (\<forall>f. face_of3 f p \<and> has_aff_dim3 f 2 \<longrightarrow>
          card {e. face_of3 e p \<and> has_aff_dim3 e 1 \<and> e \<subseteq> f} = m) \<and>
       (\<forall>v. face_of3 v p \<and> has_aff_dim3 v 0 \<longrightarrow>
          card {e. face_of3 e p \<and> has_aff_dim3 e 1 \<and> v \<subseteq> e} = n))
     \<longleftrightarrow>
       (m = 3 \<and> n = 3) \<or>
       (m = 4 \<and> n = 3) \<or>
       (m = 3 \<and> n = 4) \<or>
       (m = 5 \<and> n = 3) \<or>
       (m = 3 \<and> n = 5)"
  sorry

end
