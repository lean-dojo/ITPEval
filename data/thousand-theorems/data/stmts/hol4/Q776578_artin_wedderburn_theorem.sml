(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q776578, "Artin–Wedderburn theorem": every semisimple algebra is isomorphic
  to a finite product of nonzero-size matrix algebras over division algebras.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q776578_comm_semiring_def = new_definition (
  "q776578_comm_semiring_def",
  ``q776578_comm_semiring
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k) <=>
      (!a b. addK a b = addK b a) /\
      (!a b c. addK (addK a b) c = addK a (addK b c)) /\
      (!a. addK zeroK a = a) /\
      (!a b. mulK a b = mulK b a) /\
      (!a b c. mulK (mulK a b) c = mulK a (mulK b c)) /\
      (!a. mulK oneK a = a) /\
      (!a b c. mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
      (!a. mulK zeroK a = zeroK)``);

val q776578_ring_def = new_definition (
  "q776578_ring_def",
  ``q776578_ring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (negR : 'r -> 'r)
      (mulR : 'r -> 'r -> 'r) <=>
      (!a b. addR a b = addR b a) /\
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a. addR zeroR a = a) /\
      (!a. addR (negR a) a = zeroR) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a /\ mulR a oneR = a) /\
      (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
      (!a b c. mulR (addR a b) c = addR (mulR a c) (mulR b c)) /\
      (!a. mulR zeroR a = zeroR /\ mulR a zeroR = zeroR)``);

val q776578_algebra_def = new_definition (
  "q776578_algebra_def",
  ``q776578_algebra
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (algebraMap : 'k -> 'r) <=>
      algebraMap zeroK = zeroR /\
      algebraMap oneK = oneR /\
      (!a b. algebraMap (addK a b) = addR (algebraMap a) (algebraMap b)) /\
      (!a b. algebraMap (mulK a b) = mulR (algebraMap a) (algebraMap b)) /\
      (!a x. mulR (algebraMap a) x = mulR x (algebraMap a))``);

val q776578_left_ideal_def = new_definition (
  "q776578_left_ideal_def",
  ``q776578_left_ideal
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (I : 'r set) <=>
      zeroR IN I /\
      (!x y. x IN I /\ y IN I ==> addR x y IN I) /\
      (!x. x IN I ==> negR x IN I) /\
      (!a x. x IN I ==> mulR a x IN I)``);

val q776578_semisimple_ring_def = new_definition (
  "q776578_semisimple_ring_def",
  ``q776578_semisimple_ring
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r) (mulR : 'r -> 'r -> 'r) <=>
      !I : 'r set.
        q776578_left_ideal zeroR addR negR mulR I ==>
        ?J : 'r set.
          q776578_left_ideal zeroR addR negR mulR J /\
          (!x. x IN I /\ x IN J <=> x = zeroR) /\
          (!x. ?y z. y IN I /\ z IN J /\ x = addR y z)``);

val q776578_division_algebra_def = new_definition (
  "q776578_division_algebra_def",
  ``q776578_division_algebra
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (D : 'd set) (zeroD : 'd) (oneD : 'd)
      (addD : 'd -> 'd -> 'd) (negD : 'd -> 'd)
      (mulD : 'd -> 'd -> 'd) (invD : 'd -> 'd)
      (scalarD : 'k -> 'd) <=>
      zeroD IN D /\ oneD IN D /\ zeroD <> oneD /\
      (!x y. x IN D /\ y IN D ==> addD x y IN D) /\
      (!x. x IN D ==> negD x IN D) /\
      (!x y. x IN D /\ y IN D ==> mulD x y IN D) /\
      (!x. x IN D ==> invD x IN D) /\
      (!x y. x IN D /\ y IN D ==> addD x y = addD y x) /\
      (!x y z.
        x IN D /\ y IN D /\ z IN D ==>
        addD (addD x y) z = addD x (addD y z)) /\
      (!x. x IN D ==> addD zeroD x = x) /\
      (!x. x IN D ==> addD (negD x) x = zeroD) /\
      (!x y z.
        x IN D /\ y IN D /\ z IN D ==>
        mulD (mulD x y) z = mulD x (mulD y z)) /\
      (!x. x IN D ==> mulD oneD x = x /\ mulD x oneD = x) /\
      (!x y z.
        x IN D /\ y IN D /\ z IN D ==>
        mulD x (addD y z) = addD (mulD x y) (mulD x z)) /\
      (!x y z.
        x IN D /\ y IN D /\ z IN D ==>
        mulD (addD x y) z = addD (mulD x z) (mulD y z)) /\
      (!x. x IN D ==> mulD zeroD x = zeroD /\ mulD x zeroD = zeroD) /\
      invD zeroD = zeroD /\
      (!x.
        x IN D /\ x <> zeroD ==>
        mulD (invD x) x = oneD /\ mulD x (invD x) = oneD) /\
      (!a. scalarD a IN D) /\
      scalarD zeroK = zeroD /\
      scalarD oneK = oneD /\
      (!a b. scalarD (addK a b) = addD (scalarD a) (scalarD b)) /\
      (!a b. scalarD (mulK a b) = mulD (scalarD a) (scalarD b)) /\
      (!a x.
        x IN D ==> mulD (scalarD a) x = mulD x (scalarD a))``);

val q776578_matrix_space_def = new_definition (
  "q776578_matrix_space_def",
  ``q776578_matrix_space
      (n : num) (D : num -> 'd set) (d : num -> num)
      (zeroD : num -> 'd) (A : num -> num -> num -> 'd) <=>
      !i j k.
        if i < n /\ j < d i /\ k < d i
        then A i j k IN D i
        else A i j k = zeroD i``);

val q776578_matrix_zero_def = new_definition (
  "q776578_matrix_zero_def",
  ``q776578_matrix_zero
      (zeroD : num -> 'd) (i : num) (j : num) (k : num) =
      zeroD i``);

val q776578_matrix_one_def = new_definition (
  "q776578_matrix_one_def",
  ``q776578_matrix_one
      (n : num) (d : num -> num)
      (zeroD : num -> 'd) (oneD : num -> 'd)
      (i : num) (j : num) (k : num) =
      if i < n /\ j < d i /\ k < d i
      then if j = k then oneD i else zeroD i
      else zeroD i``);

val q776578_matrix_add_def = new_definition (
  "q776578_matrix_add_def",
  ``q776578_matrix_add
      (n : num) (d : num -> num)
      (zeroD : num -> 'd) (addD : num -> 'd -> 'd -> 'd)
      (A : num -> num -> num -> 'd)
      (B : num -> num -> num -> 'd)
      (i : num) (j : num) (k : num) =
      if i < n /\ j < d i /\ k < d i
      then addD i (A i j k) (B i j k)
      else zeroD i``);

val q776578_matrix_neg_def = new_definition (
  "q776578_matrix_neg_def",
  ``q776578_matrix_neg
      (n : num) (d : num -> num)
      (zeroD : num -> 'd) (negD : num -> 'd -> 'd)
      (A : num -> num -> num -> 'd)
      (i : num) (j : num) (k : num) =
      if i < n /\ j < d i /\ k < d i
      then negD i (A i j k)
      else zeroD i``);

val q776578_matrix_mul_def = new_definition (
  "q776578_matrix_mul_def",
  ``q776578_matrix_mul
      (n : num) (d : num -> num)
      (zeroD : num -> 'd)
      (addD : num -> 'd -> 'd -> 'd)
      (mulD : num -> 'd -> 'd -> 'd)
      (A : num -> num -> num -> 'd)
      (B : num -> num -> num -> 'd)
      (i : num) (j : num) (k : num) =
      if i < n /\ j < d i /\ k < d i
      then
        FOLDR (addD i) (zeroD i)
          (GENLIST (\t. mulD i (A i j t) (B i t k)) (d i))
      else zeroD i``);

val q776578_matrix_scalar_def = new_definition (
  "q776578_matrix_scalar_def",
  ``q776578_matrix_scalar
      (n : num) (d : num -> num) (zeroD : num -> 'd)
      (scalarD : num -> 'k -> 'd) (a : 'k)
      (i : num) (j : num) (k : num) =
      if i < n /\ j < d i /\ k < d i
      then if j = k then scalarD i a else zeroD i
      else zeroD i``);

val q776578_alg_equiv_def = new_definition (
  "q776578_alg_equiv_def",
  ``q776578_alg_equiv
      (n : num) (D : num -> 'd set) (d : num -> num)
      (zeroK : 'k) (oneK : 'k)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (negR : 'r -> 'r)
      (mulR : 'r -> 'r -> 'r) (algebraMap : 'k -> 'r)
      (zeroD : num -> 'd) (oneD : num -> 'd)
      (addD : num -> 'd -> 'd -> 'd)
      (negD : num -> 'd -> 'd)
      (mulD : num -> 'd -> 'd -> 'd)
      (scalarD : num -> 'k -> 'd)
      (e : 'r -> num -> num -> num -> 'd) <=>
      BIJ e UNIV
        {A | q776578_matrix_space n D d zeroD A} /\
      e zeroR = q776578_matrix_zero zeroD /\
      e oneR = q776578_matrix_one n d zeroD oneD /\
      (!x y.
        e (addR x y) =
        q776578_matrix_add n d zeroD addD (e x) (e y)) /\
      (!x.
        e (negR x) =
        q776578_matrix_neg n d zeroD negD (e x)) /\
      (!x y.
        e (mulR x y) =
        q776578_matrix_mul n d zeroD addD mulD (e x) (e y)) /\
      (!a.
        e (algebraMap a) =
        q776578_matrix_scalar n d zeroD scalarD a)``);

val IsSemisimpleRing_exists_algEquiv_pi_matrix_divisionRing =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (negR : 'r -> 'r)
      (mulR : 'r -> 'r -> 'r) (algebraMap : 'k -> 'r).
      q776578_comm_semiring zeroK oneK addK mulK /\
      q776578_ring zeroR oneR addR negR mulR /\
      q776578_algebra
        zeroK oneK addK mulK zeroR oneR addR mulR algebraMap /\
      q776578_semisimple_ring zeroR addR negR mulR
      ==>
      ?n (D : num -> ('r set) set) (d : num -> num)
       (zeroD : num -> 'r set) (oneD : num -> 'r set)
       (addD : num -> 'r set -> 'r set -> 'r set)
       (negD : num -> 'r set -> 'r set)
       (mulD : num -> 'r set -> 'r set -> 'r set)
       (invD : num -> 'r set -> 'r set)
       (scalarD : num -> 'k -> 'r set)
       (e : 'r -> num -> num -> num -> 'r set).
        (!i.
          i < n ==>
          0 < d i /\
          q776578_division_algebra
            zeroK oneK addK mulK
            (D i) (zeroD i) (oneD i)
            (addD i) (negD i) (mulD i) (invD i) (scalarD i)) /\
        q776578_alg_equiv
          n D d zeroK oneK zeroR oneR addR negR mulR algebraMap
          zeroD oneD addD negD mulD scalarD e``;
