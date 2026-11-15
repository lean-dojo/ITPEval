(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q203565, "Solutions of a general cubic equation": Cardano's three-root
  characterization over an arbitrary field in which 2 and 3 are invertible,
  with a primitive cube root of unity and the specified auxiliary roots. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory;

val q203565_field_def = new_definition (
  "q203565_field_def",
  ``q203565_field
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

val q203565_numeral_def = new_definition (
  "q203565_numeral_def",
  ``q203565_numeral
      (zeroK : 'k) (oneK : 'k) (add : 'k -> 'k -> 'k) (n : num) =
      FUNPOW (add oneK) n zeroK``);

val q203565_pow_def = new_definition (
  "q203565_pow_def",
  ``q203565_pow
      (oneK : 'k) (mul : 'k -> 'k -> 'k) (x : 'k) (n : num) =
      FUNPOW (mul x) n oneK``);

val q203565_sub_def = new_definition (
  "q203565_sub_def",
  ``q203565_sub
      (add : 'k -> 'k -> 'k) (neg : 'k -> 'k) (x : 'k) y =
      add x (neg y)``);

val q203565_div_def = new_definition (
  "q203565_div_def",
  ``q203565_div
      (mul : 'k -> 'k -> 'k) (invK : 'k -> 'k) (x : 'k) y =
      mul x (invK y)``);

val q203565_primitive_cube_root_def = new_definition (
  "q203565_primitive_cube_root_def",
  ``q203565_primitive_cube_root
      (oneK : 'k) (mul : 'k -> 'k -> 'k) (omega : 'k) <=>
      q203565_pow oneK mul omega 3 = oneK /\
      !m : num.
        0 < m /\ m < 3 ==> q203565_pow oneK mul omega m <> oneK``);

val Theorems100_cubic_eq_zero_iff =
  ``!(zeroK : 'k) oneK
      (add : 'k -> 'k -> 'k) (mul : 'k -> 'k -> 'k)
      (neg : 'k -> 'k) (invK : 'k -> 'k)
      (a : 'k) b c d omega p q r s t x.
      q203565_field zeroK oneK add mul neg invK /\
      q203565_numeral zeroK oneK add 2 <> zeroK /\
      q203565_numeral zeroK oneK add 3 <> zeroK /\
      a <> zeroK /\
      q203565_primitive_cube_root oneK mul omega /\
      p =
        q203565_div mul invK
          (q203565_sub add neg
            (mul (mul (q203565_numeral zeroK oneK add 3) a) c)
            (q203565_pow oneK mul b 2))
          (mul
            (q203565_numeral zeroK oneK add 9)
            (q203565_pow oneK mul a 2)) /\
      p <> zeroK /\
      q =
        q203565_div mul invK
          (q203565_sub add neg
            (q203565_sub add neg
              (mul
                (mul
                  (mul (q203565_numeral zeroK oneK add 9) a)
                  b)
                c)
              (mul
                (q203565_numeral zeroK oneK add 2)
                (q203565_pow oneK mul b 3)))
            (mul
              (mul
                (q203565_numeral zeroK oneK add 27)
                (q203565_pow oneK mul a 2))
              d))
          (mul
            (q203565_numeral zeroK oneK add 54)
            (q203565_pow oneK mul a 3)) /\
      q203565_pow oneK mul r 2 =
        add
          (q203565_pow oneK mul q 2)
          (q203565_pow oneK mul p 3) /\
      q203565_pow oneK mul s 3 = add q r /\
      mul t s = p
      ==>
      (add
        (add
          (add
            (mul a (q203565_pow oneK mul x 3))
            (mul b (q203565_pow oneK mul x 2)))
          (mul c x))
        d = zeroK
      <=>
      x =
        q203565_sub add neg
          (q203565_sub add neg s t)
          (q203565_div mul invK b
            (mul (q203565_numeral zeroK oneK add 3) a)) \/
      x =
        q203565_sub add neg
          (q203565_sub add neg
            (mul s omega)
            (mul t (q203565_pow oneK mul omega 2)))
          (q203565_div mul invK b
            (mul (q203565_numeral zeroK oneK add 3) a)) \/
      x =
        q203565_sub add neg
          (q203565_sub add neg
            (mul s (q203565_pow oneK mul omega 2))
            (mul t omega))
          (q203565_div mul invK b
            (mul (q203565_numeral zeroK oneK add 3) a)))``;
