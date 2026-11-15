(*
  Statement-only formalization of thousand-theorems corpus artifact Q1148215,
  "Mitchell's embedding theorem": every abelian category admits a full and
  faithful embedding into modules over a ring that preserves finite limits
  and finite colimits. This file contains no proof.
*)

theory Q1148215_mitchell_s_embedding_theorem
  imports Main
begin

record ('o, 'm) preadditive_category_data =
  objects :: "'o set"
  arrows :: "'m set"
  source :: "'m \<Rightarrow> 'o"
  target :: "'m \<Rightarrow> 'o"
  identity :: "'o \<Rightarrow> 'm"
  compose :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"
  zero_arrow :: "'o \<Rightarrow> 'o \<Rightarrow> 'm"
  add_arrow :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"
  neg_arrow :: "'m \<Rightarrow> 'm"

definition hom ::
    "('o, 'm) preadditive_category_data \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm set" where
  "hom C X Y =
    {f \<in> arrows C. source C f = X \<and> target C f = Y}"

definition is_category ::
    "('o, 'm) preadditive_category_data \<Rightarrow> bool" where
  "is_category C \<longleftrightarrow>
    (\<forall>f \<in> arrows C.
      source C f \<in> objects C \<and> target C f \<in> objects C) \<and>
    (\<forall>X \<in> objects C.
      identity C X \<in> hom C X X) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> hom C X Y. \<forall>g \<in> hom C Y Z.
        compose C g f \<in> hom C X Z) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>f \<in> hom C X Y.
        compose C (identity C Y) f = f \<and>
        compose C f (identity C X) = f) \<and>
    (\<forall>W \<in> objects C. \<forall>X \<in> objects C.
      \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> hom C W X. \<forall>g \<in> hom C X Y. \<forall>h \<in> hom C Y Z.
        compose C h (compose C g f) = compose C (compose C h g) f)"

definition is_preadditive ::
    "('o, 'm) preadditive_category_data \<Rightarrow> bool" where
  "is_preadditive C \<longleftrightarrow>
    is_category C \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      zero_arrow C X Y \<in> hom C X Y \<and>
      (\<forall>f \<in> hom C X Y. neg_arrow C f \<in> hom C X Y) \<and>
      (\<forall>f \<in> hom C X Y. \<forall>g \<in> hom C X Y.
        add_arrow C f g \<in> hom C X Y) \<and>
      (\<forall>f \<in> hom C X Y.
        add_arrow C (zero_arrow C X Y) f = f \<and>
        add_arrow C f (zero_arrow C X Y) = f) \<and>
      (\<forall>f \<in> hom C X Y.
        add_arrow C f (neg_arrow C f) = zero_arrow C X Y) \<and>
      (\<forall>f \<in> hom C X Y. \<forall>g \<in> hom C X Y.
        add_arrow C f g = add_arrow C g f) \<and>
      (\<forall>f \<in> hom C X Y. \<forall>g \<in> hom C X Y.
        \<forall>h \<in> hom C X Y.
          add_arrow C (add_arrow C f g) h =
          add_arrow C f (add_arrow C g h))) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> hom C X Y. \<forall>g \<in> hom C X Y. \<forall>h \<in> hom C Y Z.
        compose C h (add_arrow C f g) =
          add_arrow C (compose C h f) (compose C h g)) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> hom C X Y. \<forall>g \<in> hom C Y Z. \<forall>h \<in> hom C Y Z.
        compose C (add_arrow C g h) f =
          add_arrow C (compose C g f) (compose C h f))"

definition is_zero_object ::
    "('o, 'm) preadditive_category_data \<Rightarrow> 'o \<Rightarrow> bool" where
  "is_zero_object C Z \<longleftrightarrow>
    Z \<in> objects C \<and>
    (\<forall>X \<in> objects C. \<exists>!f. f \<in> hom C Z X) \<and>
    (\<forall>X \<in> objects C. \<exists>!f. f \<in> hom C X Z)"

definition is_binary_biproduct ::
    "('o, 'm) preadditive_category_data \<Rightarrow>
      'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow>
      'm \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_binary_biproduct C X Y B i1 i2 p1 p2 \<longleftrightarrow>
    X \<in> objects C \<and> Y \<in> objects C \<and> B \<in> objects C \<and>
    i1 \<in> hom C X B \<and> i2 \<in> hom C Y B \<and>
    p1 \<in> hom C B X \<and> p2 \<in> hom C B Y \<and>
    compose C p1 i1 = identity C X \<and>
    compose C p2 i2 = identity C Y \<and>
    compose C p1 i2 = zero_arrow C Y X \<and>
    compose C p2 i1 = zero_arrow C X Y \<and>
    add_arrow C (compose C i1 p1) (compose C i2 p2) = identity C B"

definition is_kernel ::
    "('o, 'm) preadditive_category_data \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_kernel C k f \<longleftrightarrow>
    k \<in> arrows C \<and> f \<in> arrows C \<and> target C k = source C f \<and>
    compose C f k = zero_arrow C (source C k) (target C f) \<and>
    (\<forall>X \<in> objects C. \<forall>h \<in> hom C X (source C f).
      compose C f h = zero_arrow C X (target C f) \<longrightarrow>
      (\<exists>!u. u \<in> hom C X (source C k) \<and> compose C k u = h))"

definition is_cokernel ::
    "('o, 'm) preadditive_category_data \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_cokernel C q f \<longleftrightarrow>
    q \<in> arrows C \<and> f \<in> arrows C \<and> source C q = target C f \<and>
    compose C q f = zero_arrow C (source C f) (target C q) \<and>
    (\<forall>X \<in> objects C. \<forall>h \<in> hom C (target C f) X.
      compose C h f = zero_arrow C (source C f) X \<longrightarrow>
      (\<exists>!u. u \<in> hom C (target C q) X \<and> compose C u q = h))"

definition is_monomorphism ::
    "('o, 'm) preadditive_category_data \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_monomorphism C f \<longleftrightarrow>
    f \<in> arrows C \<and>
    (\<forall>X \<in> objects C. \<forall>g \<in> hom C X (source C f).
      \<forall>h \<in> hom C X (source C f).
        compose C f g = compose C f h \<longrightarrow> g = h)"

definition is_epimorphism ::
    "('o, 'm) preadditive_category_data \<Rightarrow> 'm \<Rightarrow> bool" where
  "is_epimorphism C f \<longleftrightarrow>
    f \<in> arrows C \<and>
    (\<forall>X \<in> objects C. \<forall>g \<in> hom C (target C f) X.
      \<forall>h \<in> hom C (target C f) X.
        compose C g f = compose C h f \<longrightarrow> g = h)"

definition is_abelian_category ::
    "('o, 'm) preadditive_category_data \<Rightarrow> bool" where
  "is_abelian_category C \<longleftrightarrow>
    is_preadditive C \<and>
    (\<exists>Z. is_zero_object C Z) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<exists>B i1 i2 p1 p2. is_binary_biproduct C X Y B i1 i2 p1 p2) \<and>
    (\<forall>f \<in> arrows C. \<exists>k. is_kernel C k f) \<and>
    (\<forall>f \<in> arrows C. \<exists>q. is_cokernel C q f) \<and>
    (\<forall>f \<in> arrows C.
      is_monomorphism C f \<longrightarrow>
      (\<exists>q. is_cokernel C q f \<and> is_kernel C f q)) \<and>
    (\<forall>f \<in> arrows C.
      is_epimorphism C f \<longrightarrow>
      (\<exists>k. is_kernel C k f \<and> is_cokernel C f k))"

record 'r ring_data =
  ring_carrier :: "'r set"
  ring_zero :: "'r"
  ring_one :: "'r"
  ring_add :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
  ring_mul :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
  ring_neg :: "'r \<Rightarrow> 'r"

definition is_ring :: "'r ring_data \<Rightarrow> bool" where
  "is_ring R \<longleftrightarrow>
    ring_zero R \<in> ring_carrier R \<and>
    ring_one R \<in> ring_carrier R \<and>
    (\<forall>a \<in> ring_carrier R. ring_neg R a \<in> ring_carrier R) \<and>
    (\<forall>a \<in> ring_carrier R. \<forall>b \<in> ring_carrier R.
      ring_add R a b \<in> ring_carrier R \<and>
      ring_mul R a b \<in> ring_carrier R) \<and>
    (\<forall>a \<in> ring_carrier R.
      ring_add R (ring_zero R) a = a \<and>
      ring_add R a (ring_zero R) = a \<and>
      ring_add R a (ring_neg R a) = ring_zero R \<and>
      ring_mul R (ring_one R) a = a \<and>
      ring_mul R a (ring_one R) = a) \<and>
    (\<forall>a \<in> ring_carrier R. \<forall>b \<in> ring_carrier R.
      ring_add R a b = ring_add R b a) \<and>
    (\<forall>a \<in> ring_carrier R. \<forall>b \<in> ring_carrier R.
      \<forall>c \<in> ring_carrier R.
        ring_add R (ring_add R a b) c = ring_add R a (ring_add R b c) \<and>
        ring_mul R (ring_mul R a b) c = ring_mul R a (ring_mul R b c) \<and>
        ring_mul R a (ring_add R b c) =
          ring_add R (ring_mul R a b) (ring_mul R a c) \<and>
        ring_mul R (ring_add R a b) c =
          ring_add R (ring_mul R a c) (ring_mul R b c))"

record ('o, 'm, 'r, 'v) module_embedding_data =
  coefficient_ring :: "'r ring_data"
  module_carrier :: "'o \<Rightarrow> 'v set"
  module_zero :: "'o \<Rightarrow> 'v"
  module_add :: "'o \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
  module_neg :: "'o \<Rightarrow> 'v \<Rightarrow> 'v"
  scalar_mul :: "'o \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'v"
  morphism_map :: "'m \<Rightarrow> 'v \<Rightarrow> 'v"

definition is_module_at ::
    "('o, 'm, 'r, 'v) module_embedding_data \<Rightarrow> 'o \<Rightarrow> bool" where
  "is_module_at E X \<longleftrightarrow>
    module_zero E X \<in> module_carrier E X \<and>
    (\<forall>u \<in> module_carrier E X. module_neg E X u \<in> module_carrier E X) \<and>
    (\<forall>u \<in> module_carrier E X. \<forall>v \<in> module_carrier E X.
      module_add E X u v \<in> module_carrier E X) \<and>
    (\<forall>r \<in> ring_carrier (coefficient_ring E).
      \<forall>u \<in> module_carrier E X.
        scalar_mul E X r u \<in> module_carrier E X) \<and>
    (\<forall>u \<in> module_carrier E X.
      module_add E X (module_zero E X) u = u \<and>
      module_add E X u (module_zero E X) = u \<and>
      module_add E X u (module_neg E X u) = module_zero E X \<and>
      scalar_mul E X (ring_one (coefficient_ring E)) u = u \<and>
      scalar_mul E X (ring_zero (coefficient_ring E)) u = module_zero E X) \<and>
    (\<forall>u \<in> module_carrier E X. \<forall>v \<in> module_carrier E X.
      module_add E X u v = module_add E X v u) \<and>
    (\<forall>u \<in> module_carrier E X. \<forall>v \<in> module_carrier E X.
      \<forall>w \<in> module_carrier E X.
        module_add E X (module_add E X u v) w =
          module_add E X u (module_add E X v w)) \<and>
    (\<forall>r \<in> ring_carrier (coefficient_ring E).
      \<forall>s \<in> ring_carrier (coefficient_ring E).
      \<forall>u \<in> module_carrier E X. \<forall>v \<in> module_carrier E X.
        scalar_mul E X (ring_add (coefficient_ring E) r s) u =
          module_add E X (scalar_mul E X r u) (scalar_mul E X s u) \<and>
        scalar_mul E X r (module_add E X u v) =
          module_add E X (scalar_mul E X r u) (scalar_mul E X r v) \<and>
        scalar_mul E X (ring_mul (coefficient_ring E) r s) u =
          scalar_mul E X r (scalar_mul E X s u))"

definition is_linear_map ::
    "('o, 'm, 'r, 'v) module_embedding_data \<Rightarrow>
      'o \<Rightarrow> 'o \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> bool" where
  "is_linear_map E X Y L \<longleftrightarrow>
    (\<forall>u \<in> module_carrier E X. L u \<in> module_carrier E Y) \<and>
    L (module_zero E X) = module_zero E Y \<and>
    (\<forall>u \<in> module_carrier E X. \<forall>v \<in> module_carrier E X.
      L (module_add E X u v) = module_add E Y (L u) (L v)) \<and>
    (\<forall>r \<in> ring_carrier (coefficient_ring E).
      \<forall>u \<in> module_carrier E X.
        L (scalar_mul E X r u) = scalar_mul E Y r (L u))"

definition is_full_faithful_exact_module_embedding ::
    "('o, 'm) preadditive_category_data \<Rightarrow>
      ('o, 'm, 'r, 'v) module_embedding_data \<Rightarrow> bool" where
  "is_full_faithful_exact_module_embedding C E \<longleftrightarrow>
    is_ring (coefficient_ring E) \<and>
    (\<forall>X \<in> objects C. is_module_at E X) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>f \<in> hom C X Y. is_linear_map E X Y (morphism_map E f)) \<and>
    (\<forall>X \<in> objects C. \<forall>u \<in> module_carrier E X.
      morphism_map E (identity C X) u = u) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C. \<forall>Z \<in> objects C.
      \<forall>f \<in> hom C X Y. \<forall>g \<in> hom C Y Z.
      \<forall>u \<in> module_carrier E X.
        morphism_map E (compose C g f) u =
          morphism_map E g (morphism_map E f u)) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>u \<in> module_carrier E X.
        morphism_map E (zero_arrow C X Y) u = module_zero E Y) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>f \<in> hom C X Y. \<forall>g \<in> hom C X Y.
      \<forall>u \<in> module_carrier E X.
        morphism_map E (add_arrow C f g) u =
          module_add E Y (morphism_map E f u) (morphism_map E g u)) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>L. is_linear_map E X Y L \<longrightarrow>
        (\<exists>f \<in> hom C X Y.
          \<forall>u \<in> module_carrier E X. morphism_map E f u = L u)) \<and>
    (\<forall>X \<in> objects C. \<forall>Y \<in> objects C.
      \<forall>f \<in> hom C X Y. \<forall>g \<in> hom C X Y.
        (\<forall>u \<in> module_carrier E X.
          morphism_map E f u = morphism_map E g u) \<longrightarrow> f = g) \<and>
    (\<forall>k f. is_kernel C k f \<longrightarrow>
      inj_on (morphism_map E k) (module_carrier E (source C k)) \<and>
      morphism_map E k ` module_carrier E (source C k) =
        {u \<in> module_carrier E (source C f).
          morphism_map E f u = module_zero E (target C f)}) \<and>
    (\<forall>q f. is_cokernel C q f \<longrightarrow>
      morphism_map E q ` module_carrier E (source C q) =
        module_carrier E (target C q) \<and>
      {u \<in> module_carrier E (target C f).
        morphism_map E q u = module_zero E (target C q)} =
        morphism_map E f ` module_carrier E (source C f))"

(*
  HOL cannot existentially quantify over carrier types. Let kappa bound the
  object and arrow carriers (and nat). In the standard small-category
  construction, the embedding ring has cardinal at most kappa^kappa, hence at
  most 2^kappa, and its modules fit in a further powerset. These code types
  therefore retain the existential carrier freedom of the source theorem.
*)
type_synonym ('o, 'm) freyd_mitchell_ring_code = "((nat + 'o) + 'm) set"
type_synonym ('o, 'm) freyd_mitchell_vector_code =
  "('o, 'm) freyd_mitchell_ring_code set"

theorem freyd_mitchell:
  fixes C :: "('o, 'm) preadditive_category_data"
  assumes "is_abelian_category C"
  shows "\<exists>E ::
      ('o, 'm, ('o, 'm) freyd_mitchell_ring_code,
        ('o, 'm) freyd_mitchell_vector_code) module_embedding_data.
    is_full_faithful_exact_module_embedding C E"
  sorry

end
