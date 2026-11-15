(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1420905 (thousand-theorems__hol4__Q1420905), "Hilbert's theorem 90":
  for a finite-dimensional cyclic Galois field extension, every element
  whose product over the Galois automorphisms is one is a quotient of a
  nonzero element by its image under a chosen generator. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q1420905_field_def = new_definition (
  "q1420905_field_def",
  ``q1420905_field
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (invA : 'a -> 'a) <=>
      zero <> oneA /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul oneA x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      invA zero = zero /\
      (!x. x <> zero ==> mul (invA x) x = oneA)``);

val q1420905_field_embedding_def = new_definition (
  "q1420905_field_embedding_def",
  ``q1420905_field_embedding
      (Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) <=>
      embed Kzero = Lzero /\
      embed Kone = Lone /\
      (!a b. embed (Kadd a b) = Ladd (embed a) (embed b)) /\
      (!a b. embed (Kmul a b) = Lmul (embed a) (embed b)) /\
      (!a. embed (Kneg a) = Lneg (embed a)) /\
      (!a. embed (Kinv a) = Linv (embed a)) /\
      (!a b. embed a = embed b ==> a = b)``);

val q1420905_lincomb_def = new_definition (
  "q1420905_lincomb_def",
  ``q1420905_lincomb
      (Kzero : 'k)
      (Lzero : 'l) (Ladd : 'l -> 'l -> 'l)
      (Lmul : 'l -> 'l -> 'l) (embed : 'k -> 'l)
      (basis : 'l list) (coeff : num -> 'k) =
      FOLDL
        (\acc i.
          Ladd acc (Lmul (embed (coeff i)) (EL i basis)))
        Lzero
        (GENLIST (\i. i) (LENGTH basis))``);

val q1420905_basis_def = new_definition (
  "q1420905_basis_def",
  ``q1420905_basis
      (Kzero : 'k)
      (Lzero : 'l) (Ladd : 'l -> 'l -> 'l)
      (Lmul : 'l -> 'l -> 'l) (embed : 'k -> 'l)
      (basis : 'l list) <=>
      ALL_DISTINCT basis /\
      (!coeff : num -> 'k.
        q1420905_lincomb
          Kzero Lzero Ladd Lmul embed basis coeff = Lzero
        ==>
        !i. i < LENGTH basis ==> coeff i = Kzero) /\
      (!x : 'l.
        ?coeff : num -> 'k.
          q1420905_lincomb
            Kzero Lzero Ladd Lmul embed basis coeff = x)``);

val q1420905_finite_dimensional_def = new_definition (
  "q1420905_finite_dimensional_def",
  ``q1420905_finite_dimensional
      (Kzero : 'k)
      (Lzero : 'l) (Ladd : 'l -> 'l -> 'l)
      (Lmul : 'l -> 'l -> 'l) (embed : 'k -> 'l) <=>
      ?basis : 'l list.
        q1420905_basis Kzero Lzero Ladd Lmul embed basis``);

val q1420905_automorphism_def = new_definition (
  "q1420905_automorphism_def",
  ``q1420905_automorphism
      (Kzero : 'k) (Kone : 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) (sigma : 'l -> 'l) <=>
      BIJ sigma UNIV UNIV /\
      sigma Lzero = Lzero /\
      sigma Lone = Lone /\
      (!x y. sigma (Ladd x y) = Ladd (sigma x) (sigma y)) /\
      (!x y. sigma (Lmul x y) = Lmul (sigma x) (sigma y)) /\
      (!x. sigma (Lneg x) = Lneg (sigma x)) /\
      (!x. sigma (Linv x) = Linv (sigma x)) /\
      (!a. sigma (embed a) = embed a)``);

val q1420905_automorphisms_def = new_definition (
  "q1420905_automorphisms_def",
  ``q1420905_automorphisms
      (Kzero : 'k) (Kone : 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) =
      {sigma |
        q1420905_automorphism
          Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed sigma}``);

val q1420905_is_galois_def = new_definition (
  "q1420905_is_galois_def",
  ``q1420905_is_galois
      (Kzero : 'k) (Kone : 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) <=>
      FINITE
        (q1420905_automorphisms
          Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed) /\
      !basis : 'l list.
        q1420905_basis Kzero Lzero Ladd Lmul embed basis
        ==>
        CARD
          (q1420905_automorphisms
            Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed) =
        LENGTH basis``);

val q1420905_cyclic_automorphisms_def = new_definition (
  "q1420905_cyclic_automorphisms_def",
  ``q1420905_cyclic_automorphisms
      (Kzero : 'k) (Kone : 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) <=>
      ?generator : 'l -> 'l.
        generator IN
          q1420905_automorphisms
            Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed /\
        !sigma.
          sigma IN
            q1420905_automorphisms
              Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed
          ==>
          ?n : num. sigma = FUNPOW generator n``);

val q1420905_galois_norm_def = new_definition (
  "q1420905_galois_norm_def",
  ``q1420905_galois_norm
      (Kzero : 'k) (Kone : 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) (x : 'l) =
      ITSET
        (\sigma acc. Lmul (sigma x) acc)
        (q1420905_automorphisms
          Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed)
        Lone``);

val exists_div_of_norm_eq_one =
  ``!(Kzero : 'k) (Kone : 'k)
      (Kadd : 'k -> 'k -> 'k) (Kmul : 'k -> 'k -> 'k)
      (Kneg : 'k -> 'k) (Kinv : 'k -> 'k)
      (Lzero : 'l) (Lone : 'l)
      (Ladd : 'l -> 'l -> 'l) (Lmul : 'l -> 'l -> 'l)
      (Lneg : 'l -> 'l) (Linv : 'l -> 'l)
      (embed : 'k -> 'l) (g : 'l -> 'l) (x : 'l).
      q1420905_field Kzero Kone Kadd Kmul Kneg Kinv /\
      q1420905_field Lzero Lone Ladd Lmul Lneg Linv /\
      q1420905_field_embedding
        Kzero Kone Kadd Kmul Kneg Kinv
        Lzero Lone Ladd Lmul Lneg Linv embed /\
      q1420905_finite_dimensional Kzero Lzero Ladd Lmul embed /\
      q1420905_is_galois
        Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed /\
      q1420905_cyclic_automorphisms
        Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed /\
      g IN
        q1420905_automorphisms
          Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed /\
      (!sigma.
        sigma IN
          q1420905_automorphisms
            Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed
        ==>
        ?n : num. sigma = FUNPOW g n) /\
      q1420905_galois_norm
        Kzero Kone Lzero Lone Ladd Lmul Lneg Linv embed x = Lone
      ==>
      ?y : 'l.
        y <> Lzero /\
        Lmul y (Linv (g y)) = x``;
