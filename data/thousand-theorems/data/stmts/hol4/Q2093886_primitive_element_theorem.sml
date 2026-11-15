(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2093886, "Primitive element theorem": every finite-dimensional separable
  field extension is generated over its base field by one element. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q2093886_field_def = new_definition (
  "q2093886_field_def",
  ``q2093886_field
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

val q2093886_field_embedding_def = new_definition (
  "q2093886_field_embedding_def",
  ``q2093886_field_embedding
      (Fzero : 'f) (Fone : 'f)
      (Fadd : 'f -> 'f -> 'f) (Fmul : 'f -> 'f -> 'f)
      (Fneg : 'f -> 'f)
      (Ezero : 'e) (Eone : 'e)
      (Eadd : 'e -> 'e -> 'e) (Emul : 'e -> 'e -> 'e)
      (Eneg : 'e -> 'e) (embed : 'f -> 'e) <=>
      embed Fzero = Ezero /\
      embed Fone = Eone /\
      (!x y. embed (Fadd x y) = Eadd (embed x) (embed y)) /\
      (!x y. embed (Fmul x y) = Emul (embed x) (embed y)) /\
      (!x. embed (Fneg x) = Eneg (embed x)) /\
      (!x y. embed x = embed y ==> x = y)``);

val q2093886_lincomb_def = new_definition (
  "q2093886_lincomb_def",
  ``q2093886_lincomb
      (Ezero : 'e) (Eadd : 'e -> 'e -> 'e)
      (Emul : 'e -> 'e -> 'e) (embed : 'f -> 'e)
      (basis : 'e list) (coeff : num -> 'f) =
      FOLDL
        (\acc i. Eadd acc (Emul (embed (coeff i)) (EL i basis)))
        Ezero
        (GENLIST (\i. i) (LENGTH basis))``);

val q2093886_basis_def = new_definition (
  "q2093886_basis_def",
  ``q2093886_basis
      (Fzero : 'f)
      (Ezero : 'e) (Eadd : 'e -> 'e -> 'e)
      (Emul : 'e -> 'e -> 'e) (embed : 'f -> 'e)
      (basis : 'e list) <=>
      ALL_DISTINCT basis /\
      (!coeff : num -> 'f.
        q2093886_lincomb Ezero Eadd Emul embed basis coeff = Ezero ==>
        !i. i < LENGTH basis ==> coeff i = Fzero) /\
      (!x : 'e.
        ?coeff : num -> 'f.
          q2093886_lincomb Ezero Eadd Emul embed basis coeff = x)``);

val q2093886_finite_dimensional_def = new_definition (
  "q2093886_finite_dimensional_def",
  ``q2093886_finite_dimensional
      (Fzero : 'f)
      (Ezero : 'e) (Eadd : 'e -> 'e -> 'e)
      (Emul : 'e -> 'e -> 'e) (embed : 'f -> 'e) <=>
      ?basis : 'e list.
        q2093886_basis Fzero Ezero Eadd Emul embed basis``);

val q2093886_polynomial_def = new_definition (
  "q2093886_polynomial_def",
  ``q2093886_polynomial (zero : 'f) (p : num -> 'f) <=>
      FINITE {n : num | p n <> zero}``);

val q2093886_poly_mul_coeff_def = new_definition (
  "q2093886_poly_mul_coeff_def",
  ``q2093886_poly_mul_coeff
      (zero : 'f) (add : 'f -> 'f -> 'f) (mul : 'f -> 'f -> 'f)
      (p : num -> 'f) (q : num -> 'f) (n : num) =
      ITSET
        (\i acc. add (mul (p i) (q (n - i))) acc)
        (count (SUC n))
        zero``);

val q2093886_poly_unit_def = new_definition (
  "q2093886_poly_unit_def",
  ``q2093886_poly_unit (zero : 'f) (p : num -> 'f) <=>
      q2093886_polynomial zero p /\
      p 0 <> zero /\
      !n : num. p (SUC n) = zero``);

val q2093886_irreducible_def = new_definition (
  "q2093886_irreducible_def",
  ``q2093886_irreducible
      (zero : 'f) (add : 'f -> 'f -> 'f) (mul : 'f -> 'f -> 'f)
      (p : num -> 'f) <=>
      q2093886_polynomial zero p /\
      (?n : num. p n <> zero) /\
      ~q2093886_poly_unit zero p /\
      !q r : num -> 'f.
        q2093886_polynomial zero q /\
        q2093886_polynomial zero r /\
        (!n.
          p n = q2093886_poly_mul_coeff zero add mul q r n)
        ==>
        q2093886_poly_unit zero q \/
        q2093886_poly_unit zero r``);

val q2093886_numeral_def = new_definition (
  "q2093886_numeral_def",
  ``q2093886_numeral
      (zero : 'f) (oneF : 'f) (add : 'f -> 'f -> 'f) (n : num) =
      FUNPOW (add oneF) n zero``);

val q2093886_derivative_coeff_def = new_definition (
  "q2093886_derivative_coeff_def",
  ``q2093886_derivative_coeff
      (zero : 'f) (oneF : 'f)
      (add : 'f -> 'f -> 'f) (mul : 'f -> 'f -> 'f)
      (p : num -> 'f) (n : num) =
      mul (q2093886_numeral zero oneF add (SUC n)) (p (SUC n))``);

val q2093886_poly_eval_def = new_definition (
  "q2093886_poly_eval_def",
  ``q2093886_poly_eval
      (Fzero : 'f)
      (Ezero : 'e) (Eone : 'e)
      (Eadd : 'e -> 'e -> 'e) (Emul : 'e -> 'e -> 'e)
      (embed : 'f -> 'e) (p : num -> 'f) (x : 'e) =
      ITSET
        (\n acc.
          Eadd
            (Emul (embed (p n)) (FUNPOW (Emul x) n Eone))
            acc)
        {n : num | p n <> Fzero}
        Ezero``);

val q2093886_separable_element_def = new_definition (
  "q2093886_separable_element_def",
  ``q2093886_separable_element
      (Fzero : 'f) (Fone : 'f)
      (Fadd : 'f -> 'f -> 'f) (Fmul : 'f -> 'f -> 'f)
      (Ezero : 'e) (Eone : 'e)
      (Eadd : 'e -> 'e -> 'e) (Emul : 'e -> 'e -> 'e)
      (embed : 'f -> 'e) (x : 'e) <=>
      ?p : num -> 'f.
        q2093886_irreducible Fzero Fadd Fmul p /\
        q2093886_poly_eval
          Fzero Ezero Eone Eadd Emul embed p x = Ezero /\
        ?n : num.
          q2093886_derivative_coeff
            Fzero Fone Fadd Fmul p n <> Fzero``);

val q2093886_separable_extension_def = new_definition (
  "q2093886_separable_extension_def",
  ``q2093886_separable_extension
      (Fzero : 'f) (Fone : 'f)
      (Fadd : 'f -> 'f -> 'f) (Fmul : 'f -> 'f -> 'f)
      (Ezero : 'e) (Eone : 'e)
      (Eadd : 'e -> 'e -> 'e) (Emul : 'e -> 'e -> 'e)
      (embed : 'f -> 'e) <=>
      !x : 'e.
        q2093886_separable_element
          Fzero Fone Fadd Fmul
          Ezero Eone Eadd Emul embed x``);

val q2093886_subfield_def = new_definition (
  "q2093886_subfield_def",
  ``q2093886_subfield
      (zero : 'e) (oneE : 'e)
      (add : 'e -> 'e -> 'e) (mul : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (invE : 'e -> 'e) (subset : 'e -> bool) <=>
      subset zero /\
      subset oneE /\
      (!x y. subset x /\ subset y ==> subset (add x y)) /\
      (!x y. subset x /\ subset y ==> subset (mul x y)) /\
      (!x. subset x ==> subset (neg x)) /\
      (!x. subset x ==> subset (invE x))``);

val q2093886_generated_field_def = new_definition (
  "q2093886_generated_field_def",
  ``q2093886_generated_field
      (Ezero : 'e) (Eone : 'e)
      (Eadd : 'e -> 'e -> 'e) (Emul : 'e -> 'e -> 'e)
      (Eneg : 'e -> 'e) (Einv : 'e -> 'e)
      (embed : 'f -> 'e) (alpha : 'e) (x : 'e) <=>
      !subset : 'e -> bool.
        q2093886_subfield
          Ezero Eone Eadd Emul Eneg Einv subset /\
        (!c : 'f. subset (embed c)) /\
        subset alpha
        ==>
        subset x``);

val exists_primitive_element =
  ``!(Fzero : 'f) (Fone : 'f)
      (Fadd : 'f -> 'f -> 'f) (Fmul : 'f -> 'f -> 'f)
      (Fneg : 'f -> 'f) (Finv : 'f -> 'f)
      (Ezero : 'e) (Eone : 'e)
      (Eadd : 'e -> 'e -> 'e) (Emul : 'e -> 'e -> 'e)
      (Eneg : 'e -> 'e) (Einv : 'e -> 'e)
      (embed : 'f -> 'e).
      q2093886_field Fzero Fone Fadd Fmul Fneg Finv /\
      q2093886_field Ezero Eone Eadd Emul Eneg Einv /\
      q2093886_field_embedding
        Fzero Fone Fadd Fmul Fneg
        Ezero Eone Eadd Emul Eneg embed /\
      q2093886_finite_dimensional
        Fzero Ezero Eadd Emul embed /\
      q2093886_separable_extension
        Fzero Fone Fadd Fmul
        Ezero Eone Eadd Emul embed
      ==>
      ?alpha : 'e.
        !x : 'e.
          q2093886_generated_field
            Ezero Eone Eadd Emul Eneg Einv embed alpha x``;
