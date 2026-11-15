(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1227702, "Dirichlet's unit theorem": for a number field, the units of its
  ring of integers modulo roots of unity have a Z-basis of rank one less than
  the number of infinite places, and every unit has a unique decomposition
  into a root of unity times integer powers of fundamental units. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pairTheory pred_setTheory
     ratTheory realTheory complexTheory;

val q1227702_field_def = new_definition (
  "q1227702_field_def",
  ``q1227702_field
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (kinv : 'a -> 'a) <=>
      zero <> oneK /\
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul x (mul y z) = mul (mul x y) z) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneK x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      kinv zero = zero /\
      (!x. x <> zero ==> mul (kinv x) x = oneK)``);

val q1227702_rat_embedding_def = new_definition (
  "q1227702_rat_embedding_def",
  ``q1227702_rat_embedding
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (kinv : 'a -> 'a)
      (qemb : rat -> 'a) <=>
      qemb 0q = zero /\
      qemb 1q = oneK /\
      (!q r. qemb (q + r) = add (qemb q) (qemb r)) /\
      (!q r. qemb (q * r) = mul (qemb q) (qemb r)) /\
      (!q. qemb (-q) = neg (qemb q)) /\
      (!q. q <> 0q ==> qemb (rat_minv q) = kinv (qemb q)) /\
      (!q r. qemb q = qemb r ==> q = r)``);

val q1227702_lincomb_def = new_definition (
  "q1227702_lincomb_def",
  ``q1227702_lincomb
      (zero : 'a) (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (qemb : rat -> 'a) (basis : 'a list) (coeff : rat list) =
      FOLDL
        (\acc i. add acc (mul (qemb (EL i coeff)) (EL i basis)))
        zero
        (GENLIST (\i. i) (LENGTH basis))``);

val q1227702_rat_basis_def = new_definition (
  "q1227702_rat_basis_def",
  ``q1227702_rat_basis
      (zero : 'a) (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (qemb : rat -> 'a) (basis : 'a list) <=>
      !x : 'a.
        ?!coeff : rat list.
          LENGTH coeff = LENGTH basis /\
          q1227702_lincomb zero add mul qemb basis coeff = x``);

val q1227702_number_field_def = new_definition (
  "q1227702_number_field_def",
  ``q1227702_number_field
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (kinv : 'a -> 'a)
      (qemb : rat -> 'a) <=>
      q1227702_field zero oneK add mul neg kinv /\
      q1227702_rat_embedding zero oneK add mul neg kinv qemb /\
      ?basis : 'a list.
        q1227702_rat_basis zero add mul qemb basis``);

val q1227702_poly_eval_def = new_definition (
  "q1227702_poly_eval_def",
  ``q1227702_poly_eval
      (zero : 'a) (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (qemb : rat -> 'a) (coeff : int list) (x : 'a) =
      FOLDR
        (\c acc. add (qemb (rat_of_int c)) (mul x acc))
        zero
        coeff``);

val q1227702_integral_def = new_definition (
  "q1227702_integral_def",
  ``q1227702_integral
      (zero : 'a) (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (qemb : rat -> 'a) (x : 'a) <=>
      ?coeff : int list.
        coeff <> [] /\
        LAST coeff = (1 : int) /\
        q1227702_poly_eval zero add mul qemb coeff x = zero``);

val q1227702_unit_def = new_definition (
  "q1227702_unit_def",
  ``q1227702_unit
      (zero : 'a) (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (kinv : 'a -> 'a) (qemb : rat -> 'a) (x : 'a) <=>
      x <> zero /\
      q1227702_integral zero add mul qemb x /\
      q1227702_integral zero add mul qemb (kinv x)``);

val q1227702_torsion_unit_def = new_definition (
  "q1227702_torsion_unit_def",
  ``q1227702_torsion_unit
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (kinv : 'a -> 'a) (qemb : rat -> 'a) (x : 'a) <=>
      q1227702_unit zero add mul kinv qemb x /\
      ?n : num. 0 < n /\ FUNPOW (mul x) n oneK = oneK``);

val q1227702_complex_embedding_def = new_definition (
  "q1227702_complex_embedding_def",
  ``q1227702_complex_embedding
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (phi : 'a -> complex) <=>
      phi zero = 0 /\
      phi oneK = 1 /\
      (!x y. phi (add x y) = phi x + phi y) /\
      (!x y. phi (mul x y) = phi x * phi y) /\
      (!x. phi (neg x) = -phi x) /\
      (!x y. phi x = phi y ==> x = y)``);

val q1227702_infinite_places_def = new_definition (
  "q1227702_infinite_places_def",
  ``q1227702_infinite_places
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) =
      {place : ('a -> complex) set |
        ?phi : 'a -> complex.
          q1227702_complex_embedding zero oneK add mul neg phi /\
          place =
            {psi : 'a -> complex |
              q1227702_complex_embedding zero oneK add mul neg psi /\
              (psi = phi \/ psi = (\x. conj (phi x)))}}``);

val q1227702_unit_rank_def = new_definition (
  "q1227702_unit_rank_def",
  ``q1227702_unit_rank
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) =
      CARD (q1227702_infinite_places zero oneK add mul neg) - 1``);

val q1227702_int_pow_def = new_definition (
  "q1227702_int_pow_def",
  ``q1227702_int_pow
      (oneK : 'a) (mul : 'a -> 'a -> 'a) (kinv : 'a -> 'a)
      (x : 'a) (z : int) =
      if 0 <= z then FUNPOW (mul x) (Num z) oneK
      else FUNPOW (mul (kinv x)) (Num (-z)) oneK``);

val q1227702_fund_product_def = new_definition (
  "q1227702_fund_product_def",
  ``q1227702_fund_product
      (oneK : 'a) (mul : 'a -> 'a -> 'a) (kinv : 'a -> 'a)
      (fund : 'a list) (coeff : int list) =
      FOLDL
        (\acc i.
          mul acc
            (q1227702_int_pow oneK mul kinv
              (EL i fund) (EL i coeff)))
        oneK
        (GENLIST (\i. i) (LENGTH fund))``);

val q1227702_basis_mod_torsion_def = new_definition (
  "q1227702_basis_mod_torsion_def",
  ``q1227702_basis_mod_torsion
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (kinv : 'a -> 'a) (qemb : rat -> 'a)
      (rank : num) (fund : 'a list) <=>
      LENGTH fund = rank /\
      EVERY (q1227702_unit zero add mul kinv qemb) fund /\
      !x : 'a.
        q1227702_unit zero add mul kinv qemb x ==>
        ?!coeff : int list.
          LENGTH coeff = rank /\
          q1227702_torsion_unit zero oneK add mul kinv qemb
            (mul x
              (kinv
                (q1227702_fund_product oneK mul kinv fund coeff)))``);

val q1227702_fund_system_def = new_definition (
  "q1227702_fund_system_def",
  ``q1227702_fund_system
      (zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (kinv : 'a -> 'a) (qemb : rat -> 'a) (rank : num) =
      @fund : 'a list.
        q1227702_basis_mod_torsion
          zero oneK add mul kinv qemb rank fund``);

val basisModTorsion =
  ``!(zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (kinv : 'a -> 'a)
      (qemb : rat -> 'a).
      q1227702_number_field zero oneK add mul neg kinv qemb ==>
      q1227702_basis_mod_torsion
        zero oneK add mul kinv qemb
        (q1227702_unit_rank zero oneK add mul neg)
        (q1227702_fund_system
          zero oneK add mul kinv qemb
          (q1227702_unit_rank zero oneK add mul neg))``;

val exist_unique_eq_mul_prod =
  ``!(zero : 'a) (oneK : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (kinv : 'a -> 'a)
      (qemb : rat -> 'a).
      q1227702_number_field zero oneK add mul neg kinv qemb ==>
      !x : 'a.
        q1227702_unit zero add mul kinv qemb x ==>
        ?zeta : 'a. ?coeff : int list.
          q1227702_torsion_unit
            zero oneK add mul kinv qemb zeta /\
          LENGTH coeff =
            q1227702_unit_rank zero oneK add mul neg /\
          x =
            mul zeta
              (q1227702_fund_product oneK mul kinv
                (q1227702_fund_system
                  zero oneK add mul kinv qemb
                  (q1227702_unit_rank zero oneK add mul neg))
                coeff) /\
          !zeta' : 'a. !coeff' : int list.
            q1227702_torsion_unit
              zero oneK add mul kinv qemb zeta' /\
            LENGTH coeff' =
              q1227702_unit_rank zero oneK add mul neg /\
            x =
              mul zeta'
                (q1227702_fund_product oneK mul kinv
                  (q1227702_fund_system
                    zero oneK add mul kinv qemb
                    (q1227702_unit_rank zero oneK add mul neg))
                  coeff')
            ==>
            zeta' = zeta /\ coeff' = coeff``;
