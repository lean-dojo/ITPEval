(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q213603 (thousand-theorems__hol4__Q213603), "Ceva's theorem": over an
  arbitrary normed field, three concurrent cevians of an affinely independent
  triangle have cyclic distance ratios whose product is one. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val q213603_normed_affine_context_def = new_definition (
  "q213603_normed_affine_context_def",
  ``q213603_normed_affine_context
      (kzero : 'k)
      (kone : 'k)
      (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k)
      (kinv : 'k -> 'k)
      (knorm : 'k -> real)
      (vzero : 'v)
      (vadd : 'v -> 'v -> 'v)
      (vneg : 'v -> 'v)
      (smul : 'k -> 'v -> 'v)
      (vnorm : 'v -> real)
      (padd : 'v -> 'p -> 'p)
      (psub : 'p -> 'p -> 'v) <=>
      kzero <> kone /\
      (!a b. kadd a b = kadd b a) /\
      (!a b c. kadd (kadd a b) c = kadd a (kadd b c)) /\
      (!a. kadd kzero a = a) /\
      (!a. kadd (kneg a) a = kzero) /\
      (!a b. kmul a b = kmul b a) /\
      (!a b c. kmul (kmul a b) c = kmul a (kmul b c)) /\
      (!a. kmul kone a = a) /\
      (!a b c. kmul a (kadd b c) =
          kadd (kmul a b) (kmul a c)) /\
      kinv kzero = kzero /\
      (!a. a <> kzero ==> kmul (kinv a) a = kone) /\
      (!a. 0 <= knorm a) /\
      (!a. (knorm a = 0 <=> a = kzero)) /\
      (!a. knorm (kneg a) = knorm a) /\
      (!a b. knorm (kadd a b) <= knorm a + knorm b) /\
      (!a b. knorm (kmul a b) = knorm a * knorm b) /\
      (!x y. vadd x y = vadd y x) /\
      (!x y z. vadd (vadd x y) z = vadd x (vadd y z)) /\
      (!x. vadd vzero x = x) /\
      (!x. vadd (vneg x) x = vzero) /\
      (!x. 0 <= vnorm x) /\
      vnorm vzero = 0 /\
      (!x. vnorm (vneg x) = vnorm x) /\
      (!x y. vnorm (vadd x y) <= vnorm x + vnorm y) /\
      (!x. smul kone x = x) /\
      (!a b x. smul (kmul a b) x = smul a (smul b x)) /\
      (!a b x. smul (kadd a b) x =
          vadd (smul a x) (smul b x)) /\
      (!a x y. smul a (vadd x y) =
          vadd (smul a x) (smul a y)) /\
      (!a x. vnorm (smul a x) = knorm a * vnorm x) /\
      (!p. padd vzero p = p) /\
      (!u v p. padd (vadd u v) p = padd u (padd v p)) /\
      (!p q. padd (psub p q) q = p) /\
      (!v p. psub (padd v p) p = v) /\
      (!p q. (vnorm (psub p q) = 0 <=> p = q))``);

val q213603_triangle_def = new_definition (
  "q213603_triangle_def",
  ``q213603_triangle
      (kzero : 'k)
      (vzero : 'v)
      (vadd : 'v -> 'v -> 'v)
      (smul : 'k -> 'v -> 'v)
      (psub : 'p -> 'p -> 'v)
      (t0 : 'p)
      (t1 : 'p)
      (t2 : 'p) <=>
      !a b.
        vadd (smul a (psub t1 t0)) (smul b (psub t2 t0)) = vzero
        ==> a = kzero /\ b = kzero``);

val q213603_mem_line_def = new_definition (
  "q213603_mem_line_def",
  ``q213603_mem_line
      (smul : 'k -> 'v -> 'v)
      (padd : 'v -> 'p -> 'p)
      (psub : 'p -> 'p -> 'v)
      (a : 'p)
      (b : 'p)
      (x : 'p) <=>
      ?r : 'k. x = padd (smul r (psub b a)) a``);

val q213603_dist_def = new_definition (
  "q213603_dist_def",
  ``q213603_dist
      (vnorm : 'v -> real)
      (psub : 'p -> 'p -> 'v)
      (p : 'p)
      (q : 'p) =
      vnorm (psub p q)``);

val ceva_s_theorem =
  ``!(kzero : 'k)
      (kone : 'k)
      (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k)
      (kinv : 'k -> 'k)
      (knorm : 'k -> real)
      (vzero : 'v)
      (vadd : 'v -> 'v -> 'v)
      (vneg : 'v -> 'v)
      (smul : 'k -> 'v -> 'v)
      (vnorm : 'v -> real)
      (padd : 'v -> 'p -> 'p)
      (psub : 'p -> 'p -> 'v)
      (t0 t1 t2 p0 p1 p2 p' : 'p).
      q213603_normed_affine_context
        kzero kone kadd kmul kneg kinv knorm
        vzero vadd vneg smul vnorm padd psub /\
      q213603_triangle kzero vzero vadd smul psub t0 t1 t2 /\
      p0 <> t2 /\ p1 <> t0 /\ p2 <> t1 /\
      q213603_mem_line smul padd psub t1 t2 p0 /\
      q213603_mem_line smul padd psub t2 t0 p1 /\
      q213603_mem_line smul padd psub t0 t1 p2 /\
      q213603_mem_line smul padd psub t0 p0 p' /\
      q213603_mem_line smul padd psub t1 p1 p' /\
      q213603_mem_line smul padd psub t2 p2 p'
      ==>
      q213603_dist vnorm psub t1 p0 /
          q213603_dist vnorm psub p0 t2 *
        (q213603_dist vnorm psub t2 p1 /
          q213603_dist vnorm psub p1 t0) *
        (q213603_dist vnorm psub t0 p2 /
          q213603_dist vnorm psub p2 t1) = 1``;
