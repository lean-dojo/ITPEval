(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q476776, "Solutions of a general quartic equation": the four-root
  characterization over an arbitrary field in which 2 is invertible, using a
  root of the cubic resolvent and the specified square roots. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory;

val q476776_field_def = new_definition (
  "q476776_field_def",
  ``q476776_field
      (zeroK : 'k) (oneK : 'k)
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k) <=>
      zeroK <> oneK /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add zeroK x = x) /\
      (!x. add (neg x) x = zeroK) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul oneK x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      invK zeroK = zeroK /\
      (!x. x <> zeroK ==> mul (invK x) x = oneK)``);

val q476776_numeral_def = new_definition (
  "q476776_numeral_def",
  ``q476776_numeral
      (zeroK : 'k) (oneK : 'k) (add : 'k -> 'k -> 'k) (n : num) =
      FUNPOW (add oneK) n zeroK``);

val q476776_pow_def = new_definition (
  "q476776_pow_def",
  ``q476776_pow
      (oneK : 'k) (mul : 'k -> 'k -> 'k) (x : 'k) (n : num) =
      FUNPOW (mul x) n oneK``);

val q476776_sub_def = new_definition (
  "q476776_sub_def",
  ``q476776_sub
      (add : 'k -> 'k -> 'k) (neg : 'k -> 'k) (x : 'k) y =
      add x (neg y)``);

val q476776_div_def = new_definition (
  "q476776_div_def",
  ``q476776_div
      (mul : 'k -> 'k -> 'k) (invK : 'k -> 'k) (x : 'k) y =
      mul x (invK y)``);

val Theorems100_quartic_eq_zero_iff =
  ``!(zeroK : 'k) oneK
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k)
      (a : 'k) b c d e p q r s u v w x.
      q476776_field zeroK oneK add mul neg invK /\
      q476776_numeral zeroK oneK add 2 <> zeroK /\
      a <> zeroK /\
      p =
        q476776_div mul invK
          (q476776_sub add neg
            (mul
              (mul
                (q476776_numeral zeroK oneK add 8)
                a)
              c)
            (mul
              (q476776_numeral zeroK oneK add 3)
              (q476776_pow oneK mul b 2)))
          (mul
            (q476776_numeral zeroK oneK add 8)
            (q476776_pow oneK mul a 2)) /\
      q =
        q476776_div mul invK
          (add
            (q476776_sub add neg
              (q476776_pow oneK mul b 3)
              (mul
                (mul
                  (mul
                    (q476776_numeral zeroK oneK add 4)
                    a)
                  b)
                c))
            (mul
              (mul
                (q476776_numeral zeroK oneK add 8)
                (q476776_pow oneK mul a 2))
              d))
          (mul
            (q476776_numeral zeroK oneK add 8)
            (q476776_pow oneK mul a 3)) /\
      q <> zeroK /\
      r =
        q476776_div mul invK
          (q476776_sub add neg
            (q476776_sub add neg
              (add
                (mul
                  (mul
                    (mul
                      (q476776_numeral zeroK oneK add 16)
                      a)
                    (q476776_pow oneK mul b 2))
                  c)
                (mul
                  (mul
                    (q476776_numeral zeroK oneK add 256)
                    (q476776_pow oneK mul a 3))
                  e))
              (mul
                (q476776_numeral zeroK oneK add 3)
                (q476776_pow oneK mul b 4)))
            (mul
              (mul
                (mul
                  (q476776_numeral zeroK oneK add 64)
                  (q476776_pow oneK mul a 2))
                b)
              d))
          (mul
            (q476776_numeral zeroK oneK add 256)
            (q476776_pow oneK mul a 4)) /\
      q476776_sub add neg
        (add
          (q476776_sub add neg
            (q476776_sub add neg
              (q476776_pow oneK mul u 3)
              (mul p (q476776_pow oneK mul u 2)))
            (mul
              (mul
                (q476776_numeral zeroK oneK add 4)
                r)
              u))
          (mul
            (mul
              (q476776_numeral zeroK oneK add 4)
              p)
            r))
        (q476776_pow oneK mul q 2) = zeroK /\
      q476776_pow oneK mul s 2 =
        q476776_sub add neg u p /\
      q476776_pow oneK mul v 2 =
        q476776_sub add neg
          (mul
            (q476776_numeral zeroK oneK add 4)
            (q476776_pow oneK mul s 2))
          (mul
            (q476776_numeral zeroK oneK add 8)
            (q476776_sub add neg
              u
              (q476776_div mul invK q s))) /\
      q476776_pow oneK mul w 2 =
        q476776_sub add neg
          (mul
            (q476776_numeral zeroK oneK add 4)
            (q476776_pow oneK mul s 2))
          (mul
            (q476776_numeral zeroK oneK add 8)
            (add u (q476776_div mul invK q s)))
      ==>
      (add
        (add
          (add
            (add
              (mul a (q476776_pow oneK mul x 4))
              (mul b (q476776_pow oneK mul x 3)))
            (mul c (q476776_pow oneK mul x 2)))
          (mul d x))
        e = zeroK
      <=>
      x =
        q476776_sub add neg
          (q476776_div mul invK
            (q476776_sub add neg
              (mul (neg (q476776_numeral zeroK oneK add 2)) s)
              v)
            (q476776_numeral zeroK oneK add 4))
          (q476776_div mul invK b
            (mul (q476776_numeral zeroK oneK add 4) a)) \/
      x =
        q476776_sub add neg
          (q476776_div mul invK
            (add
              (mul (neg (q476776_numeral zeroK oneK add 2)) s)
              v)
            (q476776_numeral zeroK oneK add 4))
          (q476776_div mul invK b
            (mul (q476776_numeral zeroK oneK add 4) a)) \/
      x =
        q476776_sub add neg
          (q476776_div mul invK
            (q476776_sub add neg
              (mul (q476776_numeral zeroK oneK add 2) s)
              w)
            (q476776_numeral zeroK oneK add 4))
          (q476776_div mul invK b
            (mul (q476776_numeral zeroK oneK add 4) a)) \/
      x =
        q476776_sub add neg
          (q476776_div mul invK
            (add
              (mul (q476776_numeral zeroK oneK add 2) s)
              w)
            (q476776_numeral zeroK oneK add 4))
          (q476776_div mul invK b
            (mul (q476776_numeral zeroK oneK add 4) a)))``;
