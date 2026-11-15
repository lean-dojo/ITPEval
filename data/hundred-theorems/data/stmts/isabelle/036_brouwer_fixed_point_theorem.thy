(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light) and LCP
*)

(* At the moment this is just Brouwer's fixpoint theorem. The proof is from  *)
(* Kuhn: "some combinatorial lemmas in topology", IBM J. v4. (1960) p. 518   *)
(* See "http://www.research.ibm.com/journal/rd/045/ibmrd0405K.pdf".          *)
(*                                                                           *)
(* The script below is quite messy, but at least we avoid formalizing any    *)
(* topological machinery; we don't even use barycentric subdivision; this is *)
(* the big advantage of Kuhn's proof over the usual Sperner's lemma one.     *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)

section \<open>Brouwer's Fixed Point Theorem\<close>

theory Brouwer_Fixpoint
  imports Homeomorphism Derivative
begin

subsection \<open>Retractions\<close>

lemma retract_of_contractible:
  assumes "contractible T" "S retract_of T"
  shows "contractible S"
  by sorry

lemma retract_of_path_connected:
    "\<lbrakk>path_connected T; S retract_of T\<rbrakk> \<Longrightarrow> path_connected S"
  by sorry

lemma retract_of_simply_connected:
  assumes T: "simply_connected T" and "S retract_of T"
  shows "simply_connected S"
  by sorry

lemma retract_of_homotopically_trivial:
  assumes ts: "T retract_of S"
      and hom: "\<And>f g. \<lbrakk>continuous_on U f; f \<in> U \<rightarrow> S;
                       continuous_on U g; g \<in> U \<rightarrow> S\<rbrakk>
                       \<Longrightarrow> homotopic_with_canon (\<lambda>x. True) U S f g"
      and "continuous_on U f" "f \<in> U \<rightarrow> T"
      and "continuous_on U g" "g \<in> U \<rightarrow> T"
    shows "homotopic_with_canon (\<lambda>x. True) U T f g"
  by sorry

lemma retract_of_homotopically_trivial_null:
  assumes ts: "T retract_of S"
      and hom: "\<And>f. \<lbrakk>continuous_on U f; f \<in> U \<rightarrow> S\<rbrakk>
                     \<Longrightarrow> \<exists>c. homotopic_with_canon (\<lambda>x. True) U S f (\<lambda>x. c)"
      and "continuous_on U f" "f \<in> U \<rightarrow> T"
  obtains c where "homotopic_with_canon (\<lambda>x. True) U T f (\<lambda>x. c)"
  by sorry

lemma retraction_openin_vimage_iff:
  "openin (top_of_set S) (S \<inter> r -` U) \<longleftrightarrow> openin (top_of_set T) U"
  if "retraction S T r" and "U \<subseteq> T"
  by sorry

lemma retract_of_locally_compact:
    fixes S :: "'a :: {heine_borel,real_normed_vector} set"
    shows  "\<lbrakk> locally compact S; T retract_of S\<rbrakk> \<Longrightarrow> locally compact T"
  by sorry

lemma homotopic_into_retract:
  assumes fg: "f \<in> S \<rightarrow> T" "g \<in> S \<rightarrow> T"
  assumes "T retract_of U"
  assumes "homotopic_with_canon (\<lambda>x. True) S U f g"
  shows "homotopic_with_canon (\<lambda>x. True) S T f g"
  by sorry

lemma retract_of_locally_connected:
  assumes "locally connected T" "S retract_of T"
  shows "locally connected S"
  by sorry

lemma retract_of_locally_path_connected:
  assumes "locally path_connected T" "S retract_of T"
  shows "locally path_connected S"
  by sorry

text \<open>A few simple lemmas about deformation retracts\<close>

lemma deformation_retract_imp_homotopy_eqv:
  fixes S :: "'a::euclidean_space set"
  assumes "homotopic_with_canon (\<lambda>x. True) S S id r" and r: "retraction S T r"
  shows "S homotopy_eqv T"
  by sorry

lemma deformation_retract:
  fixes S :: "'a::euclidean_space set"
    shows "(\<exists>r. homotopic_with_canon (\<lambda>x. True) S S id r \<and> retraction S T r) \<longleftrightarrow>
           T retract_of S \<and> (\<exists>f. homotopic_with_canon (\<lambda>x. True) S S id f \<and> f \<in> S \<rightarrow> T)"
    (is "?lhs = ?rhs")
  by sorry

lemma deformation_retract_of_contractible_sing:
  fixes S :: "'a::euclidean_space set"
  assumes "contractible S" "a \<in> S"
  obtains r where "homotopic_with_canon (\<lambda>x. True) S S id r" "retraction S {a} r"
  by sorry


lemma continuous_on_compact_surface_projection_aux:
  fixes S :: "'a::t2_space set"
  assumes "compact S" "S \<subseteq> T" "image q T \<subseteq> S"
      and contp: "continuous_on T p"
      and "\<And>x. x \<in> S \<Longrightarrow> q x = x"
      and [simp]: "\<And>x. x \<in> T \<Longrightarrow> q(p x) = q x"
      and "\<And>x. x \<in> T \<Longrightarrow> p(q x) = p x"
    shows "continuous_on T q"
  by sorry

lemma continuous_on_compact_surface_projection:
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S"
      and S: "S \<subseteq> V - {0}" and "cone V"
      and iff: "\<And>x k. x \<in> V - {0} \<Longrightarrow> 0 < k \<and> (k *\<^sub>R x) \<in> S \<longleftrightarrow> d x = k"
  shows "continuous_on (V - {0}) (\<lambda>x. d x *\<^sub>R x)"
  by sorry

subsection \<open>Kuhn Simplices\<close>

lemma bij_betw_singleton_eq:
  assumes f: "bij_betw f A B" and g: "bij_betw g A B" and a: "a \<in> A"
  assumes eq: "(\<And>x. x \<in> A \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x = g x)"
  shows "f a = g a"
  by sorry

lemmas swap_apply1 = swap_apply(1)
lemmas swap_apply2 = swap_apply(2)

lemma pointwise_minimal_pointwise_maximal:
  fixes s :: "(nat \<Rightarrow> nat) set"
  assumes "finite s"
    and "s \<noteq> {}"
    and "\<forall>x\<in>s. \<forall>y\<in>s. x \<le> y \<or> y \<le> x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. a \<le> x"
    and "\<exists>a\<in>s. \<forall>x\<in>s. x \<le> a"
  by sorry

lemma kuhn_labelling_lemma:
  fixes P Q :: "'a::euclidean_space \<Rightarrow> bool"
  assumes "\<forall>x. P x \<longrightarrow> P (f x)"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i\<in>Basis. Q i \<longrightarrow> 0 \<le> x\<bullet>i \<and> x\<bullet>i \<le> 1)"
  shows "\<exists>l. (\<forall>x.\<forall>i\<in>Basis. l x i \<le> (1::nat)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x\<bullet>i \<le> f x\<bullet>i) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f x\<bullet>i \<le> x\<bullet>i)"
  by sorry


subsubsection \<open>The key "counting" observation, somewhat abstracted\<close>

lemma kuhn_counting_lemma:
  fixes bnd compo compo' face S F
  defines "nF s == card {f\<in>F. face f s \<and> compo' f}"
  assumes [simp, intro]: "finite F" \<comment> \<open>faces\<close> and [simp, intro]: "finite S" \<comment> \<open>simplices\<close>
    and "\<And>f. f \<in> F \<Longrightarrow> bnd f \<Longrightarrow> card {s\<in>S. face f s} = 1"
    and "\<And>f. f \<in> F \<Longrightarrow> \<not> bnd f \<Longrightarrow> card {s\<in>S. face f s} = 2"
    and "\<And>s. s \<in> S \<Longrightarrow> compo s \<Longrightarrow> nF s = 1"
    and "\<And>s. s \<in> S \<Longrightarrow> \<not> compo s \<Longrightarrow> nF s = 0 \<or> nF s = 2"
    and "odd (card {f\<in>F. compo' f \<and> bnd f})"
  shows "odd (card {s\<in>S. compo s})"
  by sorry

subsubsection \<open>The odd/even result for faces of complete vertices, generalized\<close>

lemma kuhn_complete_lemma:
  assumes [simp]: "finite simplices"
    and face: "\<And>f s. face f s \<longleftrightarrow> (\<exists>a\<in>s. f = s - {a})"
    and card_s[simp]:  "\<And>s. s \<in> simplices \<Longrightarrow> card s = n + 2"
    and rl_bd: "\<And>s. s \<in> simplices \<Longrightarrow> rl ` s \<subseteq> {..Suc n}"
    and bnd: "\<And>f s. s \<in> simplices \<Longrightarrow> face f s \<Longrightarrow> bnd f \<Longrightarrow> card {s\<in>simplices. face f s} = 1"
    and nbnd: "\<And>f s. s \<in> simplices \<Longrightarrow> face f s \<Longrightarrow> \<not> bnd f \<Longrightarrow> card {s\<in>simplices. face f s} = 2"
    and odd_card: "odd (card {f. (\<exists>s\<in>simplices. face f s) \<and> rl ` f = {..n} \<and> bnd f})"
  shows "odd (card {s\<in>simplices. (rl ` s = {..Suc n})})"
  by sorry

locale kuhn_simplex =
  fixes p n and base upd and S :: "(nat \<Rightarrow> nat) set"
  assumes base: "base \<in> {..< n} \<rightarrow> {..< p}"
  assumes base_out: "\<And>i. n \<le> i \<Longrightarrow> base i = p"
  assumes upd: "bij_betw upd {..< n} {..< n}"
  assumes s_pre: "S = (\<lambda>i j. if j \<in> upd`{..< i} then Suc (base j) else base j) ` {.. n}"
begin

definition "enum i j = (if j \<in> upd`{..< i} then Suc (base j) else base j)"

lemma s_eq: "S = enum ` {.. n}"
  by sorry

lemma upd_space: "i < n \<Longrightarrow> upd i < n"
  by sorry

lemma s_space: "S \<subseteq> {..< n} \<rightarrow> {.. p}"
  by sorry

lemma inj_upd: "inj_on upd {..< n}"
  by sorry

lemma inj_enum: "inj_on enum {.. n}"
  by sorry

lemma enum_0: "enum 0 = base"
  by sorry

lemma base_in_s: "base \<in> S"
  by sorry

lemma enum_in: "i \<le> n \<Longrightarrow> enum i \<in> S"
  by sorry

lemma one_step:
  assumes a: "a \<in> S" "j < n"
  assumes *: "\<And>a'. a' \<in> S \<Longrightarrow> a' \<noteq> a \<Longrightarrow> a' j = p'"
  shows "a j \<noteq> p'"
  by sorry

lemma upd_inj: "i < n \<Longrightarrow> j < n \<Longrightarrow> upd i = upd j \<longleftrightarrow> i = j"
  by sorry

lemma upd_surj: "upd ` {..< n} = {..< n}"
  by sorry

lemma in_upd_image: "A \<subseteq> {..< n} \<Longrightarrow> i < n \<Longrightarrow> upd i \<in> upd ` A \<longleftrightarrow> i \<in> A"
  by sorry

lemma enum_inj: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i = enum j \<longleftrightarrow> i = j"
  by sorry

lemma in_enum_image: "A \<subseteq> {.. n} \<Longrightarrow> i \<le> n \<Longrightarrow> enum i \<in> enum ` A \<longleftrightarrow> i \<in> A"
  by sorry

lemma enum_mono: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i \<le> enum j \<longleftrightarrow> i \<le> j"
  by sorry

lemma enum_strict_mono: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i < enum j \<longleftrightarrow> i < j"
  by sorry

lemma chain: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<le> b \<or> b \<le> a"
  by sorry

lemma less: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a i < b i \<Longrightarrow> a < b"
  by sorry

lemma enum_0_bot: "a \<in> S \<Longrightarrow> a = enum 0 \<longleftrightarrow> (\<forall>a'\<in>S. a \<le> a')"
  by sorry

lemma enum_n_top: "a \<in> S \<Longrightarrow> a = enum n \<longleftrightarrow> (\<forall>a'\<in>S. a' \<le> a)"
  by sorry

lemma enum_Suc: "i < n \<Longrightarrow> enum (Suc i) = (enum i)(upd i := Suc (enum i (upd i)))"
  by sorry

lemma enum_eq_p: "i \<le> n \<Longrightarrow> n \<le> j \<Longrightarrow> enum i j = p"
  by sorry

lemma out_eq_p: "a \<in> S \<Longrightarrow> n \<le> j \<Longrightarrow> a j = p"
  by sorry

lemma s_le_p: "a \<in> S \<Longrightarrow> a j \<le> p"
  by sorry

lemma le_Suc_base: "a \<in> S \<Longrightarrow> a j \<le> Suc (base j)"
  by sorry

lemma base_le: "a \<in> S \<Longrightarrow> base j \<le> a j"
  by sorry

lemma enum_le_p: "i \<le> n \<Longrightarrow> j < n \<Longrightarrow> enum i j \<le> p"
  by sorry

lemma enum_less: "a \<in> S \<Longrightarrow> i < n \<Longrightarrow> enum i < a \<longleftrightarrow> enum (Suc i) \<le> a"
  by sorry

lemma ksimplex_0:
  "n = 0 \<Longrightarrow> S = {(\<lambda>x. p)}"
  by sorry

lemma replace_0:
  assumes "j < n" "a \<in> S" and p: "\<forall>x\<in>S - {a}. x j = 0" and "x \<in> S"
  shows "x \<le> a"
  by sorry

lemma replace_1:
  assumes "j < n" "a \<in> S" and p: "\<forall>x\<in>S - {a}. x j = p" and "x \<in> S"
  shows "a \<le> x"
  by sorry

end

locale kuhn_simplex_pair = s: kuhn_simplex p n b_s u_s s + t: kuhn_simplex p n b_t u_t t
  for p n b_s u_s s b_t u_t t
begin

lemma enum_eq:
  assumes l: "i \<le> l" "l \<le> j" and "j + d \<le> n"
  assumes eq: "s.enum ` {i .. j} = t.enum ` {i + d .. j + d}"
  shows "s.enum l = t.enum (l + d)"
  by sorry

lemma ksimplex_eq_bot:
  assumes a: "a \<in> s" "\<And>a'. a' \<in> s \<Longrightarrow> a \<le> a'"
  assumes b: "b \<in> t" "\<And>b'. b' \<in> t \<Longrightarrow> b \<le> b'"
  assumes eq: "s - {a} = t - {b}"
  shows "s = t"
  by sorry

lemma ksimplex_eq_top:
  assumes a: "a \<in> s" "\<And>a'. a' \<in> s \<Longrightarrow> a' \<le> a"
  assumes b: "b \<in> t" "\<And>b'. b' \<in> t \<Longrightarrow> b' \<le> b"
  assumes eq: "s - {a} = t - {b}"
  shows "s = t"
  by sorry

end

inductive ksimplex for p n :: nat where
  ksimplex: "kuhn_simplex p n base upd s \<Longrightarrow> ksimplex p n s"

lemma finite_ksimplexes: "finite {s. ksimplex p n s}"
  by sorry

lemma ksimplex_card:
  assumes "ksimplex p n s" shows "card s = Suc n"
  by sorry

lemma simplex_top_face:
  assumes "0 < p" "\<forall>x\<in>s'. x n = p"
  shows "ksimplex p n s' \<longleftrightarrow> (\<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> s' = s - {a})"
  by sorry

lemma ksimplex_replace_0:
  assumes s: "ksimplex p n s" and a: "a \<in> s"
  assumes j: "j < n" and p: "\<forall>x\<in>s - {a}. x j = 0"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
  by sorry

lemma ksimplex_replace_1:
  assumes s: "ksimplex p n s" and a: "a \<in> s"
  assumes j: "j < n" and p: "\<forall>x\<in>s - {a}. x j = p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
  by sorry

lemma ksimplex_replace_2:
  assumes s: "ksimplex p n s" and "a \<in> s" and "n \<noteq> 0"
    and lb: "\<forall>j<n. \<exists>x\<in>s - {a}. x j \<noteq> 0"
    and ub: "\<forall>j<n. \<exists>x\<in>s - {a}. x j \<noteq> p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 2"
  by sorry

text \<open>Hence another step towards concreteness.\<close>

lemma kuhn_simplex_lemma:
  assumes "\<forall>s. ksimplex p (Suc n) s \<longrightarrow> rl ` s \<subseteq> {.. Suc n}"
    and "odd (card {f. \<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> (f = s - {a}) \<and>
      rl ` f = {..n} \<and> ((\<exists>j\<le>n. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>f. x j = p))})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> rl ` s = {..Suc n}})"
  by sorry

subsubsection \<open>Reduced labelling\<close>

definition reduced :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where "reduced n x = (LEAST k. k = n \<or> x k \<noteq> 0)"

lemma reduced_labelling:
  shows "reduced n x \<le> n"
    and "\<forall>i<reduced n x. x i = 0"
    and "reduced n x = n \<or> x (reduced n x) \<noteq> 0"
  by sorry

lemma reduced_labelling_unique:
  "r \<le> n \<Longrightarrow> \<forall>i<r. x i = 0 \<Longrightarrow> r = n \<or> x r \<noteq> 0 \<Longrightarrow> reduced n x = r"
  by sorry

lemma reduced_labelling_zero: "j < n \<Longrightarrow> x j = 0 \<Longrightarrow> reduced n x \<noteq> j"
  by sorry

lemma reduce_labelling_zero[simp]: "reduced 0 x = 0"
  by sorry

lemma reduced_labelling_nonzero: "j < n \<Longrightarrow> x j \<noteq> 0 \<Longrightarrow> reduced n x \<le> j"
  by sorry

lemma reduced_labelling_Suc: "reduced (Suc n) x \<noteq> Suc n \<Longrightarrow> reduced (Suc n) x = reduced n x"
  by sorry

lemma complete_face_top:
  assumes "\<forall>x\<in>f. \<forall>j\<le>n. x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x\<in>f. \<forall>j\<le>n. x j = p \<longrightarrow> lab x j = 1"
    and eq: "(reduced (Suc n) \<circ> lab) ` f = {..n}"
  shows "((\<exists>j\<le>n. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>f. x j = p)) \<longleftrightarrow> (\<forall>x\<in>f. x n = p)"
  by sorry

text \<open>Hence we get just about the nice induction.\<close>

lemma kuhn_induction:
  assumes "0 < p"
    and lab_0: "\<forall>x. \<forall>j\<le>n. (\<forall>j. x j \<le> p) \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and lab_1: "\<forall>x. \<forall>j\<le>n. (\<forall>j. x j \<le> p) \<and> x j = p \<longrightarrow> lab x j = 1"
    and odd: "odd (card {s. ksimplex p n s \<and> (reduced n\<circ>lab) ` s = {..n}})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> (reduced (Suc n)\<circ>lab) ` s = {..Suc n}})"
  by sorry

text \<open>And so we get the final combinatorial result.\<close>

lemma ksimplex_0: "ksimplex p 0 s \<longleftrightarrow> s = {(\<lambda>x. p)}"
  by sorry

lemma kuhn_combinatorial:
  assumes "0 < p"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> j < n \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> j < n  \<and> x j = p \<longrightarrow> lab x j = 1"
  shows "odd (card {s. ksimplex p n s \<and> (reduced n\<circ>lab) ` s = {..n}})"
    (is "odd (card (?M n))")
  by sorry

lemma kuhn_lemma:
  fixes n p :: nat
  assumes "0 < p"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. label x i = (0::nat) \<or> label x i = 1)"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = 0 \<longrightarrow> label x i = 0)"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = p \<longrightarrow> label x i = 1)"
  obtains q where "\<forall>i<n. q i < p"
    and "\<forall>i<n. \<exists>r s. (\<forall>j<n. q j \<le> r j \<and> r j \<le> q j + 1) \<and> (\<forall>j<n. q j \<le> s j \<and> s j \<le> q j + 1) \<and> label r i \<noteq> label s i"
  by sorry

subsubsection \<open>Main result for the unit cube\<close>

lemma kuhn_labelling_lemma':
  assumes "(\<forall>x::nat\<Rightarrow>real. P x \<longrightarrow> P (f x))"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i::nat. Q i \<longrightarrow> 0 \<le> x i \<and> x i \<le> 1)"
  shows "\<exists>l. (\<forall>x i. l x i \<le> (1::nat)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 0 \<longrightarrow> l x i = 0) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 1 \<longrightarrow> l x i = 1) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 0 \<longrightarrow> x i \<le> f x i) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 1 \<longrightarrow> f x i \<le> x i)"
  by sorry

subsection \<open>Brouwer's fixed point theorem\<close>

text \<open>We start proving Brouwer's fixed point theorem for the unit cube = \<open>cbox 0 One\<close>.\<close>

lemma brouwer_cube:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "continuous_on (cbox 0 One) f"
    and "f ` cbox 0 One \<subseteq> cbox 0 One"
  shows "\<exists>x\<in>cbox 0 One. f x = x"
  by sorry

text \<open>Next step is to prove it for nonempty interiors.\<close>

lemma brouwer_weak:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "compact S"
    and "convex S"
    and "interior S \<noteq> {}"
    and "continuous_on S f"
    and "f \<in> S \<rightarrow> S"
  obtains x where "x \<in> S" and "f x = x"
  by sorry

text \<open>Then the particular case for closed balls.\<close>

lemma brouwer_ball:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "e > 0"
    and "continuous_on (cball a e) f"
    and "f \<in> cball a e \<rightarrow> cball a e"
  obtains x where "x \<in> cball a e" and "f x = x"
  by sorry

text \<open>And finally we prove Brouwer's fixed point theorem in its general version.\<close>

theorem brouwer:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "compact S" "convex S" "S \<noteq> {}"
    and contf: "continuous_on S f"
    and fim: "f \<in> S \<rightarrow> S"
  obtains x where "x \<in> S" and "f x = x"
  by sorry

subsection \<open>Applications\<close>

text \<open>So we get the no-retraction theorem.\<close>

corollary no_retraction_cball:
  fixes a :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<not> (frontier (cball a e) retract_of (cball a e))"
  by sorry

corollary contractible_sphere:
  fixes a :: "'a::euclidean_space"
  shows "contractible(sphere a r) \<longleftrightarrow> r \<le> 0"
  by sorry

corollary connected_sphere_eq:
  fixes a :: "'a :: euclidean_space"
  shows "connected(sphere a r) \<longleftrightarrow> 2 \<le> DIM('a) \<or> r \<le> 0"
    (is "?lhs = ?rhs")
  by sorry

corollary path_connected_sphere_eq:
  fixes a :: "'a :: euclidean_space"
  shows "path_connected(sphere a r) \<longleftrightarrow> 2 \<le> DIM('a) \<or> r \<le> 0"
         (is "?lhs = ?rhs")
  by sorry

proposition frontier_subset_retraction:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" and fros: "frontier S \<subseteq> T"
      and contf: "continuous_on (closure S) f"
      and fim: "f \<in> S \<rightarrow> T"
      and fid: "\<And>x. x \<in> T \<Longrightarrow> f x = x"
    shows "S \<subseteq> T"
  by sorry

subsubsection \<open>Punctured affine hulls, etc\<close>

lemma rel_frontier_deformation_retract_of_punctured_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "convex T" "bounded S"
      and arelS: "a \<in> rel_interior S"
      and relS: "rel_frontier S \<subseteq> T"
      and affS: "T \<subseteq> affine hull S"
  obtains r where "homotopic_with_canon (\<lambda>x. True) (T - {a}) (T - {a}) id r"
                  "retraction (T - {a}) (rel_frontier S) r"
  by sorry

corollary rel_frontier_retract_of_punctured_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" "convex S" "a \<in> rel_interior S"
    shows "rel_frontier S retract_of (affine hull S - {a})"
  by sorry

corollary rel_boundary_retract_of_punctured_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S" "a \<in> rel_interior S"
    shows "(S - rel_interior S) retract_of (affine hull S - {a})"
  by sorry

lemma homotopy_eqv_rel_frontier_punctured_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "a \<in> rel_interior S" "convex T" "rel_frontier S \<subseteq> T" "T \<subseteq> affine hull S"
  shows "(rel_frontier S) homotopy_eqv (T - {a})"
  by sorry

lemma homotopy_eqv_rel_frontier_punctured_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "a \<in> rel_interior S"
    shows "(rel_frontier S) homotopy_eqv (affine hull S - {a})"
  by sorry

lemma path_connected_sphere_gen:
  assumes "convex S" "bounded S" "aff_dim S \<noteq> 1"
  shows "path_connected(rel_frontier S)"
  by sorry

lemma connected_sphere_gen:
  assumes "convex S" "bounded S" "aff_dim S \<noteq> 1"
  shows "connected(rel_frontier S)"
  by sorry

subsubsection\<open>Borsuk-style characterization of separation\<close>

lemma continuous_on_Borsuk_map:
   "a \<notin> S \<Longrightarrow>  continuous_on S (\<lambda>x. inverse(norm (x-a)) *\<^sub>R (x-a))"
  by sorry

lemma Borsuk_map_into_sphere:
   "(\<lambda>x. inverse(norm (x-a)) *\<^sub>R (x-a)) \<in> S \<rightarrow> sphere 0 1 \<longleftrightarrow> (a \<notin> S)"
  by sorry

lemma Borsuk_maps_homotopic_in_path_component:
  assumes "path_component (- S) a b"
    shows "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1)
                   (\<lambda>x. inverse(norm(x-a)) *\<^sub>R (x-a))
                   (\<lambda>x. inverse(norm(x - b)) *\<^sub>R (x - b))"
  by sorry

lemma non_extensible_Borsuk_map:
  fixes a :: "'a :: euclidean_space"
  assumes "compact S" and cin: "C \<in> components(- S)" and boc: "bounded C" and "a \<in> C"
    shows "\<not> (\<exists>g. continuous_on (S \<union> C) g \<and>
                  g \<in> (S \<union> C) \<rightarrow> sphere 0 1 \<and>
                  (\<forall>x \<in> S. g x = inverse(norm(x-a)) *\<^sub>R (x-a)))"
  by sorry

subsubsection \<open>Proving surjectivity via Brouwer fixpoint theorem\<close>

lemma brouwer_surjective:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes T: "compact T" "convex T" "T \<noteq> {}"
    and f: "continuous_on T f"
    and "\<And>x y. \<lbrakk>x\<in>S; y\<in>T\<rbrakk> \<Longrightarrow> x + (y - f y) \<in> T"
    and "x \<in> S"
  shows "\<exists>y\<in>T. f y = x"
  by sorry

lemma brouwer_surjective_cball:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "continuous_on (cball a e) f"
    and "e > 0"
    and "x \<in> S"
    and "\<And>x y. \<lbrakk>x\<in>S; y\<in>cball a e\<rbrakk> \<Longrightarrow> x + (y - f y) \<in> cball a e"
  shows "\<exists>y\<in>cball a e. f y = x"
  by sorry

subsubsection \<open>Inverse function theorem\<close>

text \<open>See Sussmann: "Multidifferential calculus", Theorem 2.1.1\<close>

lemma sussmann_open_mapping:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "open S"
    and contf: "continuous_on S f"
    and "x \<in> S"
    and derf: "(f has_derivative f') (at x)"
    and "bounded_linear g'" "f' \<circ> g' = id"
    and "T \<subseteq> S"
    and x: "x \<in> interior T"
  shows "f x \<in> interior (f ` T)"
  by sorry

text \<open>Hence the following eccentric variant of the inverse function theorem.
  This has no continuity assumptions, but we do need the inverse function.
  We could put \<open>f' \<circ> g = I\<close> but this happens to fit with the minimal linear
  algebra theory I've set up so far.\<close>

lemma has_derivative_inverse_strong:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes S: "open S" "x \<in> S"
    and contf: "continuous_on S f"
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and derf: "(f has_derivative f') (at x)"
    and id: "f' \<circ> g' = id"
  shows "(g has_derivative g') (at (f x))"
  by sorry

text \<open>A rewrite based on the other domain.\<close>

lemma has_derivative_inverse_strong_x:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "open S"
    and "g y \<in> S"
    and "continuous_on S f"
    and "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and "(f has_derivative f') (at (g y))"
    and "f' \<circ> g' = id"
    and f: "f (g y) = y"
  shows "(g has_derivative g') (at y)"
  by sorry

text \<open>On a region.\<close>

theorem has_derivative_inverse_on:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "open S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f'(x)) (at x)"
    and "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and "f' x \<circ> g' x = id"
    and "x \<in> S"
  shows "(g has_derivative g'(x)) (at (f x))"
  by sorry

end
