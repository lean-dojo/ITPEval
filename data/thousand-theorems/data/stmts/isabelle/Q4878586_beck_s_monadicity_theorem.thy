(*
  Statement-only formalization of thousand-theorems corpus artifact Q4878586
  (thousand-theorems__isabelle__Q4878586), "Beck's monadicity theorem": a
  right adjoint that creates coequalizers of pairs split by the right adjoint
  is monadic. This file contains no proof.
*)

theory Q4878586_beck_s_monadicity_theorem
  imports Main
begin

record ('o, 'm) bm_category_data =
  bm_objects :: "'o set"
  bm_arrows :: "'m set"
  bm_source :: "'m \<Rightarrow> 'o"
  bm_target :: "'m \<Rightarrow> 'o"
  bm_identity :: "'o \<Rightarrow> 'm"
  bm_compose :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"

definition bm_hom ::
    "('o, 'm) bm_category_data \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm set" where
  "bm_hom C X Y =
    {f \<in> bm_arrows C. bm_source C f = X \<and> bm_target C f = Y}"

definition bm_is_category :: "('o, 'm) bm_category_data \<Rightarrow> bool" where
  "bm_is_category C \<longleftrightarrow>
    (\<forall>f \<in> bm_arrows C.
      bm_source C f \<in> bm_objects C \<and> bm_target C f \<in> bm_objects C) \<and>
    (\<forall>X \<in> bm_objects C. bm_identity C X \<in> bm_hom C X X) \<and>
    (\<forall>X \<in> bm_objects C. \<forall>Y \<in> bm_objects C. \<forall>Z \<in> bm_objects C.
      \<forall>f \<in> bm_hom C X Y. \<forall>g \<in> bm_hom C Y Z.
        bm_compose C g f \<in> bm_hom C X Z) \<and>
    (\<forall>X \<in> bm_objects C. \<forall>Y \<in> bm_objects C.
      \<forall>f \<in> bm_hom C X Y.
        bm_compose C (bm_identity C Y) f = f \<and>
        bm_compose C f (bm_identity C X) = f) \<and>
    (\<forall>W \<in> bm_objects C. \<forall>X \<in> bm_objects C.
      \<forall>Y \<in> bm_objects C. \<forall>Z \<in> bm_objects C.
      \<forall>f \<in> bm_hom C W X. \<forall>g \<in> bm_hom C X Y.
      \<forall>h \<in> bm_hom C Y Z.
        bm_compose C h (bm_compose C g f) =
          bm_compose C (bm_compose C h g) f)"

record ('co, 'cm, 'do, 'dm) bm_functor_data =
  bm_obj_map :: "'co \<Rightarrow> 'do"
  bm_mor_map :: "'cm \<Rightarrow> 'dm"

definition bm_is_functor ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow> bool" where
  "bm_is_functor C D F \<longleftrightarrow>
    (\<forall>X \<in> bm_objects C. bm_obj_map F X \<in> bm_objects D) \<and>
    (\<forall>X \<in> bm_objects C. \<forall>Y \<in> bm_objects C.
      \<forall>f \<in> bm_hom C X Y.
        bm_mor_map F f \<in> bm_hom D (bm_obj_map F X) (bm_obj_map F Y)) \<and>
    (\<forall>X \<in> bm_objects C.
      bm_mor_map F (bm_identity C X) = bm_identity D (bm_obj_map F X)) \<and>
    (\<forall>X \<in> bm_objects C. \<forall>Y \<in> bm_objects C. \<forall>Z \<in> bm_objects C.
      \<forall>f \<in> bm_hom C X Y. \<forall>g \<in> bm_hom C Y Z.
        bm_mor_map F (bm_compose C g f) =
          bm_compose D (bm_mor_map F g) (bm_mor_map F f))"

record ('co, 'cm, 'do, 'dm) bm_adjunction_data =
  bm_unit :: "'co \<Rightarrow> 'cm"
  bm_counit :: "'do \<Rightarrow> 'dm"

definition bm_is_adjunction ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_adjunction_data \<Rightarrow> bool" where
  "bm_is_adjunction C D F G A \<longleftrightarrow>
    (\<forall>X \<in> bm_objects C.
      bm_unit A X \<in>
        bm_hom C X (bm_obj_map G (bm_obj_map F X))) \<and>
    (\<forall>Y \<in> bm_objects D.
      bm_counit A Y \<in>
        bm_hom D (bm_obj_map F (bm_obj_map G Y)) Y) \<and>
    (\<forall>X \<in> bm_objects C. \<forall>Y \<in> bm_objects C.
      \<forall>f \<in> bm_hom C X Y.
        bm_compose C
            (bm_mor_map G (bm_mor_map F f)) (bm_unit A X) =
          bm_compose C (bm_unit A Y) f) \<and>
    (\<forall>Y \<in> bm_objects D. \<forall>Z \<in> bm_objects D.
      \<forall>f \<in> bm_hom D Y Z.
        bm_compose D f (bm_counit A Y) =
          bm_compose D (bm_counit A Z)
            (bm_mor_map F (bm_mor_map G f))) \<and>
    (\<forall>X \<in> bm_objects C.
      bm_compose D (bm_counit A (bm_obj_map F X))
          (bm_mor_map F (bm_unit A X)) =
        bm_identity D (bm_obj_map F X)) \<and>
    (\<forall>Y \<in> bm_objects D.
      bm_compose C (bm_mor_map G (bm_counit A Y))
          (bm_unit A (bm_obj_map G Y)) =
        bm_identity C (bm_obj_map G Y))"

definition bm_is_coequalizer ::
    "('o, 'm) bm_category_data \<Rightarrow>
      'm \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> bool" where
  "bm_is_coequalizer C f g Q q \<longleftrightarrow>
    f \<in> bm_arrows C \<and>
    g \<in> bm_hom C (bm_source C f) (bm_target C f) \<and>
    Q \<in> bm_objects C \<and>
    q \<in> bm_hom C (bm_target C f) Q \<and>
    bm_compose C q f = bm_compose C q g \<and>
    (\<forall>R \<in> bm_objects C. \<forall>r \<in> bm_hom C (bm_target C f) R.
      bm_compose C r f = bm_compose C r g \<longrightarrow>
      (\<exists>!u. u \<in> bm_hom C Q R \<and> bm_compose C u q = r))"

definition bm_is_split_coequalizer ::
    "('o, 'm) bm_category_data \<Rightarrow>
      'm \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" where
  "bm_is_split_coequalizer C f g Q q s t \<longleftrightarrow>
    f \<in> bm_arrows C \<and>
    g \<in> bm_hom C (bm_source C f) (bm_target C f) \<and>
    Q \<in> bm_objects C \<and>
    q \<in> bm_hom C (bm_target C f) Q \<and>
    s \<in> bm_hom C Q (bm_target C f) \<and>
    t \<in> bm_hom C (bm_target C f) (bm_source C f) \<and>
    bm_compose C q f = bm_compose C q g \<and>
    bm_compose C q s = bm_identity C Q \<and>
    bm_compose C g t = bm_identity C (bm_target C f) \<and>
    bm_compose C f t = bm_compose C s q"

definition bm_is_G_split_pair ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      'dm \<Rightarrow> 'dm \<Rightarrow> bool" where
  "bm_is_G_split_pair C D G f g \<longleftrightarrow>
    f \<in> bm_arrows D \<and>
    g \<in> bm_hom D (bm_source D f) (bm_target D f) \<and>
    (\<exists>Q q s t.
      bm_is_split_coequalizer C
        (bm_mor_map G f) (bm_mor_map G g) Q q s t)"

definition bm_creates_coequalizer ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      'dm \<Rightarrow> 'dm \<Rightarrow> bool" where
  "bm_creates_coequalizer C D G f g \<longleftrightarrow>
    f \<in> bm_arrows D \<and>
    g \<in> bm_hom D (bm_source D f) (bm_target D f) \<and>
    (\<forall>Q q.
      bm_is_coequalizer C (bm_mor_map G f) (bm_mor_map G g) Q q \<longrightarrow>
      (\<exists>Q' p i j.
        Q' \<in> bm_objects D \<and>
        p \<in> bm_hom D (bm_target D f) Q' \<and>
        bm_compose D p f = bm_compose D p g \<and>
        i \<in> bm_hom C (bm_obj_map G Q') Q \<and>
        j \<in> bm_hom C Q (bm_obj_map G Q') \<and>
        bm_compose C j i = bm_identity C (bm_obj_map G Q') \<and>
        bm_compose C i j = bm_identity C Q \<and>
        bm_compose C i (bm_mor_map G p) = q)) \<and>
    (\<forall>Q' p.
      Q' \<in> bm_objects D \<longrightarrow>
      p \<in> bm_hom D (bm_target D f) Q' \<longrightarrow>
      bm_compose D p f = bm_compose D p g \<longrightarrow>
      bm_is_coequalizer C (bm_mor_map G f) (bm_mor_map G g)
        (bm_obj_map G Q') (bm_mor_map G p) \<longrightarrow>
      bm_is_coequalizer D f g Q' p)"

definition bm_creates_G_split_coequalizers ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow> bool" where
  "bm_creates_G_split_coequalizers C D G \<longleftrightarrow>
    (\<forall>X \<in> bm_objects D. \<forall>Y \<in> bm_objects D.
      \<forall>f \<in> bm_hom D X Y. \<forall>g \<in> bm_hom D X Y.
        bm_is_G_split_pair C D G f g \<longrightarrow>
        bm_creates_coequalizer C D G f g)"

definition bm_monad_obj ::
    "('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow> 'co \<Rightarrow> 'co" where
  "bm_monad_obj F G X = bm_obj_map G (bm_obj_map F X)"

definition bm_monad_map ::
    "('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow> 'cm \<Rightarrow> 'cm" where
  "bm_monad_map F G f = bm_mor_map G (bm_mor_map F f)"

definition bm_monad_mult ::
    "('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_adjunction_data \<Rightarrow> 'co \<Rightarrow> 'cm" where
  "bm_monad_mult F G A X =
    bm_mor_map G (bm_counit A (bm_obj_map F X))"

definition bm_is_algebra ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_adjunction_data \<Rightarrow>
      'co \<Rightarrow> 'cm \<Rightarrow> bool" where
  "bm_is_algebra C F G A X a \<longleftrightarrow>
    X \<in> bm_objects C \<and>
    a \<in> bm_hom C (bm_monad_obj F G X) X \<and>
    bm_compose C a (bm_unit A X) = bm_identity C X \<and>
    bm_compose C a (bm_monad_mult F G A X) =
      bm_compose C a (bm_monad_map F G a)"

definition bm_is_algebra_hom ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      'co \<Rightarrow> 'cm \<Rightarrow> 'co \<Rightarrow> 'cm \<Rightarrow> 'cm \<Rightarrow> bool" where
  "bm_is_algebra_hom C F G X a Y b h \<longleftrightarrow>
    h \<in> bm_hom C X Y \<and>
    bm_compose C h a =
      bm_compose C b (bm_monad_map F G h)"

definition bm_comparison_structure ::
    "('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_adjunction_data \<Rightarrow> 'do \<Rightarrow> 'cm" where
  "bm_comparison_structure G A Y = bm_mor_map G (bm_counit A Y)"

definition bm_comparison_is_equivalence ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_functor_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow>
      ('co, 'cm, 'do, 'dm) bm_adjunction_data \<Rightarrow> bool" where
  "bm_comparison_is_equivalence C D F G A \<longleftrightarrow>
    (\<forall>Y \<in> bm_objects D.
      bm_is_algebra C F G A (bm_obj_map G Y)
        (bm_comparison_structure G A Y)) \<and>
    (\<forall>Y \<in> bm_objects D. \<forall>Z \<in> bm_objects D.
      bij_betw (bm_mor_map G) (bm_hom D Y Z)
        {h. bm_is_algebra_hom C F G
          (bm_obj_map G Y) (bm_comparison_structure G A Y)
          (bm_obj_map G Z) (bm_comparison_structure G A Z) h}) \<and>
    (\<forall>X a.
      bm_is_algebra C F G A X a \<longrightarrow>
      (\<exists>Y u v.
        Y \<in> bm_objects D \<and>
        bm_is_algebra_hom C F G X a
          (bm_obj_map G Y) (bm_comparison_structure G A Y) u \<and>
        bm_is_algebra_hom C F G
          (bm_obj_map G Y) (bm_comparison_structure G A Y) X a v \<and>
        bm_compose C v u = bm_identity C X \<and>
        bm_compose C u v = bm_identity C (bm_obj_map G Y)))"

definition bm_is_monadic_right_adjoint ::
    "('co, 'cm) bm_category_data \<Rightarrow>
      ('do, 'dm) bm_category_data \<Rightarrow>
      ('do, 'dm, 'co, 'cm) bm_functor_data \<Rightarrow> bool" where
  "bm_is_monadic_right_adjoint C D G \<longleftrightarrow>
    bm_is_category C \<and>
    bm_is_category D \<and>
    bm_is_functor D C G \<and>
    (\<exists>F A.
      bm_is_functor C D F \<and>
      bm_is_adjunction C D F G A \<and>
      bm_comparison_is_equivalence C D F G A)"

theorem beck_monadicity:
  fixes C :: "('co, 'cm) bm_category_data"
    and D :: "('do, 'dm) bm_category_data"
    and F :: "('co, 'cm, 'do, 'dm) bm_functor_data"
    and G :: "('do, 'dm, 'co, 'cm) bm_functor_data"
    and A :: "('co, 'cm, 'do, 'dm) bm_adjunction_data"
  assumes "bm_is_category C"
    and "bm_is_category D"
    and "bm_is_functor C D F"
    and "bm_is_functor D C G"
    and "bm_is_adjunction C D F G A"
    and "bm_creates_G_split_coequalizers C D G"
  shows "bm_is_monadic_right_adjoint C D G"
  sorry

end
