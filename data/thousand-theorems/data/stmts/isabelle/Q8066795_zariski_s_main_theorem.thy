(*
  Statement-only formalization of thousand-theorems corpus artifact Q8066795
  (thousand-theorems__isabelle__Q8066795), "Zariski's main theorem": a proper
  scheme morphism locally of finite type with finite fiber over a point becomes
  finite after restriction over an open neighborhood of that point. This file
  contains no proof.

  Carrier-independent encoding and bidirectional equivalence. Isabelle/ZF's
  object type i is the universe of sets, so each ring, topological space,
  scheme, and morphism code below contains its own carrier sets; no common
  ambient carrier, finite table, same-carrier index type, or selected code
  universe is used. A scheme code is a sheaf of commutative rings on a
  topological space, locally covered by opens identified with prime spectra.
  A morphism code is a continuous map with compatible maps on sections whose
  induced stalk maps are local. Thus ordinary schemes and scheme morphisms
  encode and decode without changing their carriers.

  The predicate q8066795_is_pullback is the categorical universal property,
  quantified over every set-coded source scheme and every compatible pair of
  set-coded morphisms. Consequently it supplies every base change directly;
  there is no pullback-closure or fullness assumption hidden in properness.
  Universal closedness quantifies over every base morphism and every object
  satisfying that pullback property. Separatedness is closedness of the
  diagonal. Hence q8066795_is_proper is definitionally exactly
  separated + universally closed + locally of finite type, the three fields
  of Mathlib's AlgebraicGeometry.IsProper. The affine coordinate-ring
  definitions of locally finite type and finite morphism, the literal finite
  point fiber, and the explicit open restriction are invariant under the
  encoding and decoding. These clauses give both directions of equivalence
  with the canonical Mathlib statement, including its (redundant but explicit)
  LocallyOfFiniteType assumption.
*)

theory Q8066795_zariski_s_main_theorem
  imports ZF.Cardinal
begin

subsection \<open>Set-coded commutative rings\<close>

definition q8066795_ring_carrier :: "i \<Rightarrow> i" where
  "q8066795_ring_carrier(R) \<equiv> fst(R)"

definition q8066795_ring_zero :: "i \<Rightarrow> i" where
  "q8066795_ring_zero(R) \<equiv> fst(snd(R))"

definition q8066795_ring_one :: "i \<Rightarrow> i" where
  "q8066795_ring_one(R) \<equiv> fst(snd(snd(R)))"

definition q8066795_ring_add :: "i \<Rightarrow> i" where
  "q8066795_ring_add(R) \<equiv> fst(snd(snd(snd(R))))"

definition q8066795_ring_mul :: "i \<Rightarrow> i" where
  "q8066795_ring_mul(R) \<equiv> fst(snd(snd(snd(snd(R)))))"

definition q8066795_ring_neg :: "i \<Rightarrow> i" where
  "q8066795_ring_neg(R) \<equiv> snd(snd(snd(snd(snd(R)))))"

definition q8066795_is_comm_ring :: "i \<Rightarrow> o" where
  "q8066795_is_comm_ring(R) \<equiv>
    q8066795_ring_zero(R) \<in> q8066795_ring_carrier(R) \<and>
    q8066795_ring_one(R) \<in> q8066795_ring_carrier(R) \<and>
    q8066795_ring_neg(R) \<in>
      q8066795_ring_carrier(R) \<rightarrow> q8066795_ring_carrier(R) \<and>
    q8066795_ring_add(R) \<in>
      (q8066795_ring_carrier(R) \<times> q8066795_ring_carrier(R))
        \<rightarrow> q8066795_ring_carrier(R) \<and>
    q8066795_ring_mul(R) \<in>
      (q8066795_ring_carrier(R) \<times> q8066795_ring_carrier(R))
        \<rightarrow> q8066795_ring_carrier(R) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(R).
      q8066795_ring_add(R)`\<langle>a,q8066795_ring_zero(R)\<rangle> = a \<and>
      q8066795_ring_add(R)`\<langle>a,q8066795_ring_neg(R)`a\<rangle> =
        q8066795_ring_zero(R) \<and>
      q8066795_ring_mul(R)`\<langle>a,q8066795_ring_one(R)\<rangle> = a) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(R).
      \<forall>b\<in>q8066795_ring_carrier(R).
        q8066795_ring_add(R)`\<langle>a,b\<rangle> =
          q8066795_ring_add(R)`\<langle>b,a\<rangle> \<and>
        q8066795_ring_mul(R)`\<langle>a,b\<rangle> =
          q8066795_ring_mul(R)`\<langle>b,a\<rangle>) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(R).
      \<forall>b\<in>q8066795_ring_carrier(R).
      \<forall>c\<in>q8066795_ring_carrier(R).
        q8066795_ring_add(R)`\<langle>q8066795_ring_add(R)`\<langle>a,b\<rangle>,c\<rangle> =
          q8066795_ring_add(R)`\<langle>a,q8066795_ring_add(R)`\<langle>b,c\<rangle>\<rangle> \<and>
        q8066795_ring_mul(R)`\<langle>q8066795_ring_mul(R)`\<langle>a,b\<rangle>,c\<rangle> =
          q8066795_ring_mul(R)`\<langle>a,q8066795_ring_mul(R)`\<langle>b,c\<rangle>\<rangle> \<and>
        q8066795_ring_mul(R)`\<langle>a,q8066795_ring_add(R)`\<langle>b,c\<rangle>\<rangle> =
          q8066795_ring_add(R)`
            \<langle>q8066795_ring_mul(R)`\<langle>a,b\<rangle>,
             q8066795_ring_mul(R)`\<langle>a,c\<rangle>\<rangle>)"

definition q8066795_ring_hom :: "[i,i,i] \<Rightarrow> o" where
  "q8066795_ring_hom(A,B,f) \<equiv>
    q8066795_is_comm_ring(A) \<and> q8066795_is_comm_ring(B) \<and>
    f \<in> q8066795_ring_carrier(A) \<rightarrow> q8066795_ring_carrier(B) \<and>
    f`q8066795_ring_zero(A) = q8066795_ring_zero(B) \<and>
    f`q8066795_ring_one(A) = q8066795_ring_one(B) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(A).
      f`(q8066795_ring_neg(A)`a) = q8066795_ring_neg(B)`(f`a)) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(A).
      \<forall>b\<in>q8066795_ring_carrier(A).
        f`(q8066795_ring_add(A)`\<langle>a,b\<rangle>) =
          q8066795_ring_add(B)`\<langle>f`a,f`b\<rangle> \<and>
        f`(q8066795_ring_mul(A)`\<langle>a,b\<rangle>) =
          q8066795_ring_mul(B)`\<langle>f`a,f`b\<rangle>)"

definition q8066795_is_unit :: "[i,i] \<Rightarrow> o" where
  "q8066795_is_unit(R,a) \<equiv>
    a \<in> q8066795_ring_carrier(R) \<and>
    (\<exists>b\<in>q8066795_ring_carrier(R).
      q8066795_ring_mul(R)`\<langle>a,b\<rangle> = q8066795_ring_one(R))"

definition q8066795_is_ideal :: "[i,i] \<Rightarrow> o" where
  "q8066795_is_ideal(R,I) \<equiv>
    I \<subseteq> q8066795_ring_carrier(R) \<and>
    q8066795_ring_zero(R) \<in> I \<and>
    (\<forall>a\<in>I. q8066795_ring_neg(R)`a \<in> I) \<and>
    (\<forall>a\<in>I. \<forall>b\<in>I. q8066795_ring_add(R)`\<langle>a,b\<rangle> \<in> I) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(R).
      \<forall>b\<in>I. q8066795_ring_mul(R)`\<langle>a,b\<rangle> \<in> I)"

definition q8066795_is_prime_ideal :: "[i,i] \<Rightarrow> o" where
  "q8066795_is_prime_ideal(R,P) \<equiv>
    q8066795_is_ideal(R,P) \<and> P \<noteq> q8066795_ring_carrier(R) \<and>
    (\<forall>a\<in>q8066795_ring_carrier(R).
      \<forall>b\<in>q8066795_ring_carrier(R).
        q8066795_ring_mul(R)`\<langle>a,b\<rangle> \<in> P \<longrightarrow> a\<in>P \<or> b\<in>P)"

definition q8066795_generated_subalgebra :: "[i,i,i,i] \<Rightarrow> i" where
  "q8066795_generated_subalgebra(A,B,f,G) \<equiv>
    \<Inter>{T\<in>Pow(q8066795_ring_carrier(B)).
      f``q8066795_ring_carrier(A) \<subseteq> T \<and> G \<subseteq> T \<and>
      q8066795_ring_zero(B) \<in> T \<and> q8066795_ring_one(B) \<in> T \<and>
      (\<forall>a\<in>T. q8066795_ring_neg(B)`a \<in> T) \<and>
      (\<forall>a\<in>T. \<forall>b\<in>T.
        q8066795_ring_add(B)`\<langle>a,b\<rangle> \<in> T \<and>
        q8066795_ring_mul(B)`\<langle>a,b\<rangle> \<in> T)}"

definition q8066795_finite_type_ring_hom :: "[i,i,i] \<Rightarrow> o" where
  "q8066795_finite_type_ring_hom(A,B,f) \<equiv>
    q8066795_ring_hom(A,B,f) \<and>
    (\<exists>G\<in>Pow(q8066795_ring_carrier(B)).
      Finite(G) \<and>
      q8066795_generated_subalgebra(A,B,f,G) = q8066795_ring_carrier(B))"

definition q8066795_generated_submodule :: "[i,i,i,i] \<Rightarrow> i" where
  "q8066795_generated_submodule(A,B,f,G) \<equiv>
    \<Inter>{M\<in>Pow(q8066795_ring_carrier(B)).
      G \<subseteq> M \<and> q8066795_ring_zero(B) \<in> M \<and>
      (\<forall>x\<in>M. q8066795_ring_neg(B)`x \<in> M) \<and>
      (\<forall>x\<in>M. \<forall>y\<in>M. q8066795_ring_add(B)`\<langle>x,y\<rangle> \<in> M) \<and>
      (\<forall>a\<in>q8066795_ring_carrier(A).
        \<forall>x\<in>M. q8066795_ring_mul(B)`\<langle>f`a,x\<rangle> \<in> M)}"

definition q8066795_finite_ring_hom :: "[i,i,i] \<Rightarrow> o" where
  "q8066795_finite_ring_hom(A,B,f) \<equiv>
    q8066795_ring_hom(A,B,f) \<and>
    (\<exists>G\<in>Pow(q8066795_ring_carrier(B)).
      Finite(G) \<and>
      q8066795_generated_submodule(A,B,f,G) = q8066795_ring_carrier(B))"

definition q8066795_localization_at :: "[i,i,i,i] \<Rightarrow> o" where
  "q8066795_localization_at(A,B,f,s) \<equiv>
    q8066795_ring_hom(A,B,f) \<and> s\<in>q8066795_ring_carrier(A) \<and>
    q8066795_is_unit(B,f`s) \<and>
    (\<forall>C. \<forall>g.
      q8066795_ring_hom(A,C,g) \<and> q8066795_is_unit(C,g`s) \<longrightarrow>
      (\<exists>h. q8066795_ring_hom(B,C,h) \<and>
        (\<forall>a\<in>q8066795_ring_carrier(A). h`(f`a) = g`a) \<and>
        (\<forall>k. q8066795_ring_hom(B,C,k) \<and>
          (\<forall>a\<in>q8066795_ring_carrier(A). k`(f`a) = g`a)
          \<longrightarrow> k=h)))"

subsection \<open>Set-coded schemes\<close>

definition q8066795_points :: "i \<Rightarrow> i" where
  "q8066795_points(X) \<equiv> fst(X)"

definition q8066795_opens :: "i \<Rightarrow> i" where
  "q8066795_opens(X) \<equiv> fst(snd(X))"

definition q8066795_sections_map :: "i \<Rightarrow> i" where
  "q8066795_sections_map(X) \<equiv> fst(snd(snd(X)))"

definition q8066795_restriction_map :: "i \<Rightarrow> i" where
  "q8066795_restriction_map(X) \<equiv> snd(snd(snd(X)))"

definition q8066795_sections :: "[i,i] \<Rightarrow> i" where
  "q8066795_sections(X,U) \<equiv> q8066795_sections_map(X)`U"

definition q8066795_restricts :: "[i,i,i] \<Rightarrow> i" where
  "q8066795_restricts(X,U,V) \<equiv>
    q8066795_restriction_map(X)`\<langle>U,V\<rangle>"

definition q8066795_restriction_domain :: "i \<Rightarrow> i" where
  "q8066795_restriction_domain(X) \<equiv>
    {\<langle>U,V\<rangle> \<in> q8066795_opens(X) \<times> q8066795_opens(X). V\<subseteq>U}"

definition q8066795_is_topology :: "[i,i] \<Rightarrow> o" where
  "q8066795_is_topology(P,Opens) \<equiv>
    Opens \<subseteq> Pow(P) \<and> 0\<in>Opens \<and> P\<in>Opens \<and>
    (\<forall>C\<in>Pow(Opens). \<Union>C \<in> Opens) \<and>
    (\<forall>U\<in>Opens. \<forall>V\<in>Opens. U\<inter>V \<in> Opens)"

definition q8066795_is_ringed_space :: "i \<Rightarrow> o" where
  "q8066795_is_ringed_space(X) \<equiv>
    q8066795_is_topology(q8066795_points(X),q8066795_opens(X)) \<and>
    q8066795_sections_map(X) \<in> q8066795_opens(X) \<rightarrow> range(q8066795_sections_map(X)) \<and>
    domain(q8066795_restriction_map(X)) = q8066795_restriction_domain(X) \<and>
    function(q8066795_restriction_map(X)) \<and>
    (\<forall>U\<in>q8066795_opens(X). q8066795_is_comm_ring(q8066795_sections(X,U))) \<and>
    (\<forall>U\<in>q8066795_opens(X). \<forall>V\<in>q8066795_opens(X).
      V\<subseteq>U \<longrightarrow>
      q8066795_ring_hom(q8066795_sections(X,U),q8066795_sections(X,V),
        q8066795_restricts(X,U,V))) \<and>
    (\<forall>U\<in>q8066795_opens(X).
      \<forall>a\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
        q8066795_restricts(X,U,U)`a = a) \<and>
    (\<forall>U\<in>q8066795_opens(X). \<forall>V\<in>q8066795_opens(X).
      \<forall>W\<in>q8066795_opens(X).
      W\<subseteq>V \<and> V\<subseteq>U \<longrightarrow>
      (\<forall>a\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
        q8066795_restricts(X,V,W)`(q8066795_restricts(X,U,V)`a) =
          q8066795_restricts(X,U,W)`a)) \<and>
    (\<forall>U\<in>q8066795_opens(X). \<forall>C\<in>Pow(q8066795_opens(X)).
      \<Union>C=U \<longrightarrow>
      ((\<forall>a\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
        \<forall>b\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
          (\<forall>V\<in>C. q8066795_restricts(X,U,V)`a =
            q8066795_restricts(X,U,V)`b) \<longrightarrow> a=b) \<and>
       (\<forall>t. function(t) \<and> domain(t)=C \<and>
          (\<forall>V\<in>C. t`V \<in> q8066795_ring_carrier(q8066795_sections(X,V))) \<and>
          (\<forall>V\<in>C. \<forall>W\<in>C.
            q8066795_restricts(X,V,V\<inter>W)`(t`V) =
            q8066795_restricts(X,W,V\<inter>W)`(t`W))
          \<longrightarrow>
          (\<exists>a\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
            \<forall>V\<in>C. q8066795_restricts(X,U,V)`a=t`V))))"

definition q8066795_germ_equal :: "[i,i,i,i,i] \<Rightarrow> o" where
  "q8066795_germ_equal(X,x,U,a,b) \<equiv>
    x\<in>U \<and> U\<in>q8066795_opens(X) \<and>
    a\<in>q8066795_ring_carrier(q8066795_sections(X,U)) \<and>
    b\<in>q8066795_ring_carrier(q8066795_sections(X,U)) \<and>
    (\<exists>V\<in>q8066795_opens(X).
      x\<in>V \<and> V\<subseteq>U \<and>
      q8066795_restricts(X,U,V)`a = q8066795_restricts(X,U,V)`b)"

definition q8066795_germ_is_unit :: "[i,i,i,i] \<Rightarrow> o" where
  "q8066795_germ_is_unit(X,x,U,a) \<equiv>
    x\<in>U \<and> U\<in>q8066795_opens(X) \<and>
    a\<in>q8066795_ring_carrier(q8066795_sections(X,U)) \<and>
    (\<exists>V\<in>q8066795_opens(X). \<exists>b.
      x\<in>V \<and> V\<subseteq>U \<and>
      b\<in>q8066795_ring_carrier(q8066795_sections(X,V)) \<and>
      q8066795_ring_mul(q8066795_sections(X,V))`
        \<langle>q8066795_restricts(X,U,V)`a,b\<rangle> =
        q8066795_ring_one(q8066795_sections(X,V)))"

definition q8066795_is_locally_ringed_space :: "i \<Rightarrow> o" where
  "q8066795_is_locally_ringed_space(X) \<equiv>
    q8066795_is_ringed_space(X) \<and>
    (\<forall>x\<in>q8066795_points(X). \<forall>U\<in>q8066795_opens(X).
      x\<in>U \<longrightarrow>
      (\<forall>a\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
        q8066795_germ_is_unit(X,x,U,a) \<or>
        q8066795_germ_is_unit(X,x,U,
          q8066795_ring_add(q8066795_sections(X,U))`
            \<langle>q8066795_ring_one(q8066795_sections(X,U)),
             q8066795_ring_neg(q8066795_sections(X,U))`a\<rangle>)))"

definition q8066795_prime_spectrum :: "i \<Rightarrow> i" where
  "q8066795_prime_spectrum(R) \<equiv>
    {P\<in>Pow(q8066795_ring_carrier(R)). q8066795_is_prime_ideal(R,P)}"

definition q8066795_principal_points :: "[i,i,i,i] \<Rightarrow> i" where
  "q8066795_principal_points(X,U,e,s) \<equiv>
    {x\<in>U. s \<notin> e`x}"

definition q8066795_is_affine_open :: "[i,i] \<Rightarrow> o" where
  "q8066795_is_affine_open(X,U) \<equiv>
    U\<in>q8066795_opens(X) \<and>
    (\<exists>e. e \<in> bij(U,q8066795_prime_spectrum(q8066795_sections(X,U))) \<and>
      (\<forall>s\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
        q8066795_principal_points(X,U,e,s) \<in> q8066795_opens(X) \<and>
        q8066795_localization_at(
          q8066795_sections(X,U),
          q8066795_sections(X,q8066795_principal_points(X,U,e,s)),
          q8066795_restricts(X,U,q8066795_principal_points(X,U,e,s)),s)) \<and>
      (\<forall>W\<in>q8066795_opens(X). W\<subseteq>U \<longrightarrow>
        (\<forall>x\<in>W. \<exists>s\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
          x\<in>q8066795_principal_points(X,U,e,s) \<and>
          q8066795_principal_points(X,U,e,s)\<subseteq>W)))"

definition q8066795_is_scheme :: "i \<Rightarrow> o" where
  "q8066795_is_scheme(X) \<equiv>
    q8066795_is_locally_ringed_space(X) \<and>
    (\<forall>x\<in>q8066795_points(X). \<exists>U\<in>q8066795_opens(X).
      x\<in>U \<and> q8066795_is_affine_open(X,U))"

subsection \<open>Carrier-independent morphism codes and pullbacks\<close>

definition q8066795_source :: "i \<Rightarrow> i" where
  "q8066795_source(f) \<equiv> fst(f)"

definition q8066795_target :: "i \<Rightarrow> i" where
  "q8066795_target(f) \<equiv> fst(snd(f))"

definition q8066795_point_map :: "i \<Rightarrow> i" where
  "q8066795_point_map(f) \<equiv> fst(snd(snd(f)))"

definition q8066795_section_map :: "i \<Rightarrow> i" where
  "q8066795_section_map(f) \<equiv> snd(snd(snd(f)))"

definition q8066795_preimage :: "[i,i] \<Rightarrow> i" where
  "q8066795_preimage(f,U) \<equiv>
    {x\<in>q8066795_points(q8066795_source(f)). q8066795_point_map(f)`x \<in> U}"

definition q8066795_is_scheme_morphism :: "i \<Rightarrow> o" where
  "q8066795_is_scheme_morphism(f) \<equiv>
    q8066795_is_scheme(q8066795_source(f)) \<and>
    q8066795_is_scheme(q8066795_target(f)) \<and>
    q8066795_point_map(f) \<in>
      q8066795_points(q8066795_source(f)) \<rightarrow>
      q8066795_points(q8066795_target(f)) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      q8066795_preimage(f,U) \<in> q8066795_opens(q8066795_source(f))) \<and>
    q8066795_section_map(f) \<in>
      q8066795_opens(q8066795_target(f)) \<rightarrow> range(q8066795_section_map(f)) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      q8066795_ring_hom(
        q8066795_sections(q8066795_target(f),U),
        q8066795_sections(q8066795_source(f),q8066795_preimage(f,U)),
        q8066795_section_map(f)`U)) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      \<forall>V\<in>q8066795_opens(q8066795_target(f)).
      V\<subseteq>U \<longrightarrow>
      (\<forall>a\<in>q8066795_ring_carrier(q8066795_sections(q8066795_target(f),U)).
        q8066795_restricts(q8066795_source(f),
          q8066795_preimage(f,U),q8066795_preimage(f,V))`
          (q8066795_section_map(f)`U`a) =
        q8066795_section_map(f)`V`
          (q8066795_restricts(q8066795_target(f),U,V)`a))) \<and>
    (\<forall>x\<in>q8066795_points(q8066795_source(f)).
      \<forall>U\<in>q8066795_opens(q8066795_target(f)).
      q8066795_point_map(f)`x\<in>U \<longrightarrow>
      (\<forall>a\<in>q8066795_ring_carrier(q8066795_sections(q8066795_target(f),U)).
        q8066795_germ_is_unit(q8066795_target(f),q8066795_point_map(f)`x,U,a)
        \<longleftrightarrow>
        q8066795_germ_is_unit(q8066795_source(f),x,q8066795_preimage(f,U),
          q8066795_section_map(f)`U`a)))"

definition q8066795_morphism_equiv :: "[i,i] \<Rightarrow> o" where
  "q8066795_morphism_equiv(f,g) \<equiv>
    q8066795_is_scheme_morphism(f) \<and> q8066795_is_scheme_morphism(g) \<and>
    q8066795_source(f)=q8066795_source(g) \<and>
    q8066795_target(f)=q8066795_target(g) \<and>
    (\<forall>x\<in>q8066795_points(q8066795_source(f)).
      q8066795_point_map(f)`x=q8066795_point_map(g)`x) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      \<forall>a\<in>q8066795_ring_carrier(q8066795_sections(q8066795_target(f),U)).
        q8066795_section_map(f)`U`a=q8066795_section_map(g)`U`a)"

definition q8066795_is_identity :: "[i,i] \<Rightarrow> o" where
  "q8066795_is_identity(e,X) \<equiv>
    q8066795_is_scheme_morphism(e) \<and>
    q8066795_source(e)=X \<and> q8066795_target(e)=X \<and>
    (\<forall>x\<in>q8066795_points(X). q8066795_point_map(e)`x=x) \<and>
    (\<forall>U\<in>q8066795_opens(X).
      \<forall>a\<in>q8066795_ring_carrier(q8066795_sections(X,U)).
        q8066795_section_map(e)`U`a=a)"

definition q8066795_composes :: "[i,i,i] \<Rightarrow> o" where
  "q8066795_composes(h,f,g) \<equiv>
    q8066795_is_scheme_morphism(f) \<and> q8066795_is_scheme_morphism(g) \<and>
    q8066795_is_scheme_morphism(h) \<and>
    q8066795_target(f)=q8066795_source(g) \<and>
    q8066795_source(h)=q8066795_source(f) \<and>
    q8066795_target(h)=q8066795_target(g) \<and>
    (\<forall>x\<in>q8066795_points(q8066795_source(f)).
      q8066795_point_map(h)`x =
        q8066795_point_map(g)`(q8066795_point_map(f)`x)) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(g)).
      \<forall>a\<in>q8066795_ring_carrier(q8066795_sections(q8066795_target(g),U)).
        q8066795_section_map(h)`U`a =
        q8066795_section_map(f)`q8066795_preimage(g,U)`
          (q8066795_section_map(g)`U`a))"

definition q8066795_is_pullback :: "[i,i,i,i] \<Rightarrow> o" where
  "q8066795_is_pullback(f,g,p,q) \<equiv>
    q8066795_is_scheme_morphism(f) \<and> q8066795_is_scheme_morphism(g) \<and>
    q8066795_is_scheme_morphism(p) \<and> q8066795_is_scheme_morphism(q) \<and>
    q8066795_target(f)=q8066795_target(g) \<and>
    q8066795_target(p)=q8066795_source(f) \<and>
    q8066795_target(q)=q8066795_source(g) \<and>
    q8066795_source(p)=q8066795_source(q) \<and>
    (\<exists>c d. q8066795_composes(c,p,f) \<and>
      q8066795_composes(d,q,g) \<and> q8066795_morphism_equiv(c,d)) \<and>
    (\<forall>T. \<forall>a. \<forall>b.
      q8066795_is_scheme(T) \<and>
      q8066795_is_scheme_morphism(a) \<and> q8066795_source(a)=T \<and>
      q8066795_target(a)=q8066795_source(f) \<and>
      q8066795_is_scheme_morphism(b) \<and> q8066795_source(b)=T \<and>
      q8066795_target(b)=q8066795_source(g) \<and>
      (\<exists>c d. q8066795_composes(c,a,f) \<and>
        q8066795_composes(d,b,g) \<and> q8066795_morphism_equiv(c,d))
      \<longrightarrow>
      (\<exists>u. q8066795_is_scheme_morphism(u) \<and>
        q8066795_source(u)=T \<and>
        q8066795_target(u)=q8066795_source(p) \<and>
        (\<exists>up uq. q8066795_composes(up,u,p) \<and>
          q8066795_composes(uq,u,q) \<and>
          q8066795_morphism_equiv(up,a) \<and>
          q8066795_morphism_equiv(uq,b)) \<and>
        (\<forall>v. q8066795_is_scheme_morphism(v) \<and>
          q8066795_source(v)=T \<and>
          q8066795_target(v)=q8066795_source(p) \<and>
          (\<exists>vp vq. q8066795_composes(vp,v,p) \<and>
            q8066795_composes(vq,v,q) \<and>
            q8066795_morphism_equiv(vp,a) \<and>
            q8066795_morphism_equiv(vq,b))
          \<longrightarrow> q8066795_morphism_equiv(v,u))))"

subsection \<open>Scheme-theoretic finiteness and properness\<close>

definition q8066795_is_closed_map :: "i \<Rightarrow> o" where
  "q8066795_is_closed_map(f) \<equiv>
    q8066795_is_scheme_morphism(f) \<and>
    (\<forall>C\<in>Pow(q8066795_points(q8066795_source(f))).
      q8066795_points(q8066795_source(f))-C \<in> q8066795_opens(q8066795_source(f))
      \<longrightarrow>
      q8066795_points(q8066795_target(f))-
        (q8066795_point_map(f)``C) \<in> q8066795_opens(q8066795_target(f)))"

definition q8066795_is_affine_morphism :: "i \<Rightarrow> o" where
  "q8066795_is_affine_morphism(f) \<equiv>
    q8066795_is_scheme_morphism(f) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      q8066795_is_affine_open(q8066795_target(f),U) \<longrightarrow>
      q8066795_is_affine_open(q8066795_source(f),q8066795_preimage(f,U)))"

definition q8066795_is_closed_immersion :: "i \<Rightarrow> o" where
  "q8066795_is_closed_immersion(f) \<equiv>
    q8066795_is_affine_morphism(f) \<and> q8066795_is_closed_map(f) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      q8066795_is_affine_open(q8066795_target(f),U) \<longrightarrow>
      q8066795_section_map(f)`U \<in>
        surj(q8066795_ring_carrier(q8066795_sections(q8066795_target(f),U)),
          q8066795_ring_carrier(q8066795_sections(q8066795_source(f),
            q8066795_preimage(f,U)))))"

definition q8066795_is_separated :: "i \<Rightarrow> o" where
  "q8066795_is_separated(f) \<equiv>
    q8066795_is_scheme_morphism(f) \<and>
    (\<forall>p. \<forall>q.
      q8066795_is_pullback(f,f,p,q) \<longrightarrow>
      (\<exists>d. q8066795_is_closed_immersion(d) \<and>
        q8066795_source(d)=q8066795_source(f) \<and>
        q8066795_target(d)=q8066795_source(p) \<and>
        (\<forall>x\<in>q8066795_points(q8066795_source(f)).
          q8066795_point_map(p)`(q8066795_point_map(d)`x)=x \<and>
          q8066795_point_map(q)`(q8066795_point_map(d)`x)=x) \<and>
        (\<forall>U\<in>q8066795_opens(q8066795_source(f)).
          \<forall>a\<in>q8066795_ring_carrier(
            q8066795_sections(q8066795_source(f),U)).
            q8066795_section_map(d)`q8066795_preimage(p,U)`
              (q8066795_section_map(p)`U`a)=a \<and>
            q8066795_section_map(d)`q8066795_preimage(q,U)`
              (q8066795_section_map(q)`U`a)=a)))"

definition q8066795_is_universally_closed :: "i \<Rightarrow> o" where
  "q8066795_is_universally_closed(f) \<equiv>
    q8066795_is_scheme_morphism(f) \<and>
    (\<forall>g. q8066795_is_scheme_morphism(g) \<and>
      q8066795_target(g)=q8066795_target(f) \<longrightarrow>
      (\<forall>p. \<forall>q. q8066795_is_pullback(f,g,p,q)
        \<longrightarrow> q8066795_is_closed_map(q)))"

definition q8066795_locally_of_finite_type :: "i \<Rightarrow> o" where
  "q8066795_locally_of_finite_type(f) \<equiv>
    q8066795_is_scheme_morphism(f) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      \<forall>V\<in>q8066795_opens(q8066795_source(f)).
      q8066795_is_affine_open(q8066795_target(f),U) \<and>
      q8066795_is_affine_open(q8066795_source(f),V) \<and>
      V\<subseteq>q8066795_preimage(f,U) \<longrightarrow>
      q8066795_finite_type_ring_hom(
        q8066795_sections(q8066795_target(f),U),
        q8066795_sections(q8066795_source(f),V),
        q8066795_restricts(q8066795_source(f),q8066795_preimage(f,U),V)
          O (q8066795_section_map(f)`U)))"

definition q8066795_is_proper :: "i \<Rightarrow> o" where
  "q8066795_is_proper(f) \<equiv>
    q8066795_is_separated(f) \<and>
    q8066795_is_universally_closed(f) \<and>
    q8066795_locally_of_finite_type(f)"

definition q8066795_is_finite :: "i \<Rightarrow> o" where
  "q8066795_is_finite(f) \<equiv>
    q8066795_is_affine_morphism(f) \<and>
    (\<forall>U\<in>q8066795_opens(q8066795_target(f)).
      q8066795_is_affine_open(q8066795_target(f),U) \<longrightarrow>
      q8066795_finite_ring_hom(
        q8066795_sections(q8066795_target(f),U),
        q8066795_sections(q8066795_source(f),q8066795_preimage(f,U)),
        q8066795_section_map(f)`U))"

subsection \<open>Explicit open restriction\<close>

definition q8066795_open_subscheme :: "[i,i] \<Rightarrow> i" where
  "q8066795_open_subscheme(X,W) \<equiv>
    \<langle>W,
      {U\<in>q8066795_opens(X). U\<subseteq>W},
      restrict(q8066795_sections_map(X),{U\<in>q8066795_opens(X). U\<subseteq>W}),
      restrict(q8066795_restriction_map(X),
        {\<langle>U,V\<rangle>\<in>q8066795_restriction_domain(X). U\<subseteq>W})\<rangle>"

definition q8066795_restrict_to_open :: "[i,i] \<Rightarrow> i" where
  "q8066795_restrict_to_open(f,V) \<equiv>
    \<langle>q8066795_open_subscheme(q8066795_source(f),q8066795_preimage(f,V)),
      q8066795_open_subscheme(q8066795_target(f),V),
      restrict(q8066795_point_map(f),q8066795_preimage(f,V)),
      restrict(q8066795_section_map(f),
        {U\<in>q8066795_opens(q8066795_target(f)). U\<subseteq>V})\<rangle>"

theorem q8066795_zariski_main_local_finiteness:
  assumes morphism: "q8066795_is_scheme_morphism(f)"
    and finite_type: "q8066795_locally_of_finite_type(f)"
    and proper: "q8066795_is_proper(f)"
    and point: "y \<in> q8066795_points(q8066795_target(f))"
    and finite_fiber:
      "Finite({x\<in>q8066795_points(q8066795_source(f)).
        q8066795_point_map(f)`x = y})"
  shows "\<exists>V\<in>q8066795_opens(q8066795_target(f)).
    y\<in>V \<and> q8066795_is_finite(q8066795_restrict_to_open(f,V))"
  sorry

end
