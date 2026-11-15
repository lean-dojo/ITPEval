(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q656198, "Maschke's theorem": over a field in which the order of a finite
  group is nonzero, every invariant subspace of a linear group action has an
  invariant complementary subspace. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory pred_setTheory;

val q656198_field_def = new_definition (
  "q656198_field_def",
  ``q656198_field
      (kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k) (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k) (kinv : 'k -> 'k) <=>
      kzero <> kone /\
      (!a b. kadd a b = kadd b a) /\
      (!a b c. kadd (kadd a b) c = kadd a (kadd b c)) /\
      (!a. kadd kzero a = a) /\
      (!a. kadd (kneg a) a = kzero) /\
      (!a b. kmul a b = kmul b a) /\
      (!a b c. kmul (kmul a b) c = kmul a (kmul b c)) /\
      (!a. kmul kone a = a) /\
      (!a b c. kmul a (kadd b c) = kadd (kmul a b) (kmul a c)) /\
      kinv kzero = kzero /\
      (!a. a <> kzero ==> kmul (kinv a) a = kone)``);

val q656198_group_def = new_definition (
  "q656198_group_def",
  ``q656198_group
      (gid : 'g) (gmul : 'g -> 'g -> 'g) (ginv : 'g -> 'g) <=>
      (!g h i. gmul (gmul g h) i = gmul g (gmul h i)) /\
      (!g. gmul gid g = g /\ gmul g gid = g) /\
      (!g. gmul (ginv g) g = gid /\ gmul g (ginv g) = gid)``);

val q656198_nat_cast_def = new_definition (
  "q656198_nat_cast_def",
  ``q656198_nat_cast
      (kzero : 'k) (kone : 'k) (kadd : 'k -> 'k -> 'k) (n : num) =
      FUNPOW (kadd kone) n kzero``);

val q656198_vector_space_def = new_definition (
  "q656198_vector_space_def",
  ``q656198_vector_space
      (kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k) (kmul : 'k -> 'k -> 'k)
      (vzero : 'v) (vadd : 'v -> 'v -> 'v) (vneg : 'v -> 'v)
      (smul : 'k -> 'v -> 'v) <=>
      (!x y. vadd x y = vadd y x) /\
      (!x y z. vadd (vadd x y) z = vadd x (vadd y z)) /\
      (!x. vadd vzero x = x) /\
      (!x. vadd (vneg x) x = vzero) /\
      (!x. smul kone x = x) /\
      (!a b x. smul (kmul a b) x = smul a (smul b x)) /\
      (!a b x. smul (kadd a b) x = vadd (smul a x) (smul b x)) /\
      (!a x y. smul a (vadd x y) = vadd (smul a x) (smul a y)) /\
      (!x. smul kzero x = vzero) /\
      (!a. smul a vzero = vzero)``);

val q656198_linear_group_action_def = new_definition (
  "q656198_linear_group_action_def",
  ``q656198_linear_group_action
      (gid : 'g) (gmul : 'g -> 'g -> 'g)
      (vadd : 'v -> 'v -> 'v) (smul : 'k -> 'v -> 'v)
      (act : 'g -> 'v -> 'v) <=>
      (!x. act gid x = x) /\
      (!g h x. act (gmul g h) x = act g (act h x)) /\
      (!g x y. act g (vadd x y) = vadd (act g x) (act g y)) /\
      (!g a x. act g (smul a x) = smul a (act g x))``);

val q656198_invariant_subspace_def = new_definition (
  "q656198_invariant_subspace_def",
  ``q656198_invariant_subspace
      (vzero : 'v) (vadd : 'v -> 'v -> 'v) (vneg : 'v -> 'v)
      (smul : 'k -> 'v -> 'v) (act : 'g -> 'v -> 'v)
      (p : 'v -> bool) <=>
      p vzero /\
      (!x y. p x /\ p y ==> p (vadd x y)) /\
      (!x. p x ==> p (vneg x)) /\
      (!a x. p x ==> p (smul a x)) /\
      (!g x. p x ==> p (act g x))``);

val q656198_is_compl_def = new_definition (
  "q656198_is_compl_def",
  ``q656198_is_compl
      (vzero : 'v) (vadd : 'v -> 'v -> 'v)
      (p : 'v -> bool) (q : 'v -> bool) <=>
      (!x. p x /\ q x ==> x = vzero) /\
      (!x. ?y z. p y /\ q z /\ x = vadd y z)``);

val MonoidAlgebra_Submodule_exists_isCompl =
  ``!(kzero : 'k) (kone : 'k)
      (kadd : 'k -> 'k -> 'k) (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k) (kinv : 'k -> 'k)
      (gid : 'g) (gmul : 'g -> 'g -> 'g) (ginv : 'g -> 'g)
      (vzero : 'v) (vadd : 'v -> 'v -> 'v) (vneg : 'v -> 'v)
      (smul : 'k -> 'v -> 'v) (act : 'g -> 'v -> 'v)
      (p : 'v -> bool).
      q656198_field kzero kone kadd kmul kneg kinv /\
      q656198_group gid gmul ginv /\
      FINITE (UNIV : 'g set) /\
      q656198_nat_cast kzero kone kadd (CARD (UNIV : 'g set)) <> kzero /\
      q656198_vector_space
        kzero kone kadd kmul vzero vadd vneg smul /\
      q656198_linear_group_action gid gmul vadd smul act /\
      q656198_invariant_subspace vzero vadd vneg smul act p
      ==>
      ?q : 'v -> bool.
        q656198_invariant_subspace vzero vadd vneg smul act q /\
        q656198_is_compl vzero vadd p q``;
