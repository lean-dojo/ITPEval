(*
  Statement-only formalization of thousand-theorems corpus artifact Q1227702
  (thousand-theorems__isabelle__Q1227702), "Dirichlet's unit theorem": the
  units of the ring of integers of a number field, modulo roots of unity, have
  an integer basis indexed by the infinite places minus one, yielding a unique
  decomposition of every unit. This file contains no proof.
*)

theory Q1227702_dirichlet_s_unit_theorem
  imports Complex_Main
begin

definition q1227702_is_rat_basis ::
    "'K::field_char_0 set \<Rightarrow> bool" where
  "q1227702_is_rat_basis B \<longleftrightarrow>
    finite B \<and>
    (\<forall>x. \<exists>!c :: 'K \<Rightarrow> rat.
      (\<forall>b. b \<notin> B \<longrightarrow> c b = 0) \<and>
      x = (\<Sum>b\<in>B. of_rat (c b) * b))"

definition q1227702_is_number_field ::
    "'K::field_char_0 itself \<Rightarrow> bool" where
  "q1227702_is_number_field _ \<longleftrightarrow>
    (\<exists>B :: 'K set. q1227702_is_rat_basis B)"

definition q1227702_is_algebraic_integer ::
    "'K::field_char_0 \<Rightarrow> bool" where
  "q1227702_is_algebraic_integer x \<longleftrightarrow>
    (\<exists>c :: nat \<Rightarrow> int. \<exists>n.
      finite {i. c i \<noteq> 0} \<and>
      c n = 1 \<and>
      (\<forall>m>n. c m = 0) \<and>
      (\<Sum>i\<in>{i. c i \<noteq> 0}. of_int (c i) * x ^ i) = 0)"

definition q1227702_is_integer_unit ::
    "'K::field_char_0 \<Rightarrow> bool" where
  "q1227702_is_integer_unit u \<longleftrightarrow>
    u \<noteq> 0 \<and>
    q1227702_is_algebraic_integer u \<and>
    q1227702_is_algebraic_integer (inverse u)"

definition q1227702_is_root_of_unity ::
    "'K::field_char_0 \<Rightarrow> bool" where
  "q1227702_is_root_of_unity u \<longleftrightarrow>
    (\<exists>n>0. u ^ n = 1)"

definition q1227702_is_torsion_unit ::
    "'K::field_char_0 \<Rightarrow> bool" where
  "q1227702_is_torsion_unit u \<longleftrightarrow>
    q1227702_is_integer_unit u \<and>
    q1227702_is_root_of_unity u"

definition q1227702_is_complex_embedding ::
    "('K::field_char_0 \<Rightarrow> complex) \<Rightarrow> bool" where
  "q1227702_is_complex_embedding e \<longleftrightarrow>
    e 0 = 0 \<and>
    e 1 = 1 \<and>
    (\<forall>x y. e (x + y) = e x + e y) \<and>
    (\<forall>x y. e (x * y) = e x * e y)"

definition q1227702_complex_embeddings ::
    "('K::field_char_0 \<Rightarrow> complex) set" where
  "q1227702_complex_embeddings =
    {e. q1227702_is_complex_embedding e}"

definition q1227702_embedding_orbit ::
    "('K::field_char_0 \<Rightarrow> complex) \<Rightarrow>
      ('K \<Rightarrow> complex) set" where
  "q1227702_embedding_orbit e =
    {e, (\<lambda>x. cnj (e x))}"

definition q1227702_infinite_places ::
    "'K::field_char_0 itself \<Rightarrow> ('K \<Rightarrow> complex) set set" where
  "q1227702_infinite_places _ =
    q1227702_embedding_orbit ` q1227702_complex_embeddings"

definition q1227702_unit_rank ::
    "'K::field_char_0 itself \<Rightarrow> nat" where
  "q1227702_unit_rank K =
    card (q1227702_infinite_places K) - 1"

definition q1227702_unit_torsion_coset ::
    "'K::field_char_0 \<Rightarrow> 'K set" where
  "q1227702_unit_torsion_coset u =
    {v. q1227702_is_integer_unit v \<and>
      q1227702_is_root_of_unity (v / u)}"

definition q1227702_units_mod_torsion ::
    "'K::field_char_0 itself \<Rightarrow> 'K set set" where
  "q1227702_units_mod_torsion _ =
    {C. \<exists>u. q1227702_is_integer_unit u \<and>
      C = q1227702_unit_torsion_coset u}"

definition q1227702_coset_combination ::
    "'K::field_char_0 itself \<Rightarrow>
      (nat \<Rightarrow> 'K set) \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow>
      'K set \<Rightarrow> bool" where
  "q1227702_coset_combination K B z C \<longleftrightarrow>
    (\<exists>u :: nat \<Rightarrow> 'K.
      (\<forall>i<q1227702_unit_rank K.
        q1227702_is_integer_unit (u i) \<and>
        B i = q1227702_unit_torsion_coset (u i)) \<and>
      C = q1227702_unit_torsion_coset
        (\<Prod>i\<in>{..<q1227702_unit_rank K}. (u i) powi (z i)))"

definition q1227702_is_basis_mod_torsion ::
    "'K::field_char_0 itself \<Rightarrow> (nat \<Rightarrow> 'K set) \<Rightarrow> bool" where
  "q1227702_is_basis_mod_torsion K B \<longleftrightarrow>
    (\<forall>i<q1227702_unit_rank K.
      B i \<in> q1227702_units_mod_torsion K) \<and>
    (\<forall>C\<in>q1227702_units_mod_torsion K.
      \<exists>!z :: nat \<Rightarrow> int.
        (\<forall>i\<ge>q1227702_unit_rank K. z i = 0) \<and>
        q1227702_coset_combination K B z C)"

definition q1227702_basisModTorsion ::
    "'K::field_char_0 itself \<Rightarrow> nat \<Rightarrow> 'K set" where
  "q1227702_basisModTorsion K =
    (SOME B. q1227702_is_basis_mod_torsion K B)"

definition q1227702_fundSystem ::
    "'K::field_char_0 itself \<Rightarrow> nat \<Rightarrow> 'K" where
  "q1227702_fundSystem K =
    (\<lambda>i. SOME u.
      q1227702_is_integer_unit u \<and>
      q1227702_basisModTorsion K i =
        q1227702_unit_torsion_coset u)"

theorem q1227702_basisModTorsion_is_basis:
  assumes "q1227702_is_number_field (TYPE('K::field_char_0))"
  shows "q1227702_is_basis_mod_torsion TYPE('K)
    (q1227702_basisModTorsion TYPE('K))"
  sorry

theorem q1227702_exist_unique_eq_mul_prod:
  fixes x :: "'K::field_char_0"
  assumes "q1227702_is_number_field TYPE('K)"
    and "q1227702_is_integer_unit x"
  shows "\<exists>!ze :: 'K \<times> (nat \<Rightarrow> int).
    q1227702_is_torsion_unit (fst ze) \<and>
    (\<forall>i\<ge>q1227702_unit_rank TYPE('K). snd ze i = 0) \<and>
    x = fst ze *
      (\<Prod>i\<in>{..<q1227702_unit_rank TYPE('K)}.
        (q1227702_fundSystem TYPE('K) i) powi (snd ze i))"
  sorry

end
