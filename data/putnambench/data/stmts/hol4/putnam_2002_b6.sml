(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_b6:
  for a prime p, the determinant of the 3 by 3 matrix whose rows contain
  x, y, z and their p-th and p-squared powers is coefficientwise congruent
  modulo p to a finite product of integer linear forms ax + by + cz. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_2002_b6 =
  ``let poly_one =
        (\i j k : num.
           if i = 0 /\ j = 0 /\ k = 0 then (1 : int) else 0);
      poly_add =
        (\f g : num -> num -> num -> int.
           \i j k : num. f i j k + g i j k);
      poly_neg =
        (\f : num -> num -> num -> int.
           \i j k : num. ~(f i j k));
      poly_mul =
        (\f g : num -> num -> num -> int.
           \i j k : num.
             ITSET
               (\a acc_i.
                  ITSET
                    (\b acc_j.
                       ITSET
                         (\c acc_k.
                            f a b c * g (i - a) (j - b) (k - c) + acc_k)
                         (count (SUC k))
                         (0 : int) +
                       acc_j)
                    (count (SUC j))
                    (0 : int) +
                  acc_i)
               (count (SUC i))
               (0 : int));
      x_power =
        (\e i j k : num.
           if i = e /\ j = 0 /\ k = 0 then (1 : int) else 0);
      y_power =
        (\e i j k : num.
           if i = 0 /\ j = e /\ k = 0 then (1 : int) else 0);
      z_power =
        (\e i j k : num.
           if i = 0 /\ j = 0 /\ k = e then (1 : int) else 0);
      matrix_entry =
        (\p r c : num.
           if c = 0 then x_power (p ** r)
           else if c = 1 then y_power (p ** r)
           else z_power (p ** r));
      determinant_term =
        (\p c0 c1 c2 : num.
           poly_mul
             (matrix_entry p 0 c0)
             (poly_mul (matrix_entry p 1 c1) (matrix_entry p 2 c2)));
      determinant =
        (\p : num.
           poly_add
             (poly_add
                (poly_add
                   (determinant_term p 0 1 2)
                   (determinant_term p 1 2 0))
                (determinant_term p 2 0 1))
             (poly_add
                (poly_neg (determinant_term p 2 1 0))
                (poly_add
                   (poly_neg (determinant_term p 1 0 2))
                   (poly_neg (determinant_term p 0 2 1)))));
      linear_form =
        (\abc : int # (int # int).
           \i j k : num.
             if i = 1 /\ j = 0 /\ k = 0 then FST abc
             else if i = 0 /\ j = 1 /\ k = 0 then FST (SND abc)
             else if i = 0 /\ j = 0 /\ k = 1 then SND (SND abc)
             else 0);
      product_of_linear_forms =
        (\L : (int # (int # int)) list.
           FOLDR
             (\abc acc. poly_mul (linear_form abc) acc)
             poly_one
             L);
      poly_cong =
        (\p : num. \f g : num -> num -> num -> int.
           !i j k : num.
             int_of_num p int_divides (f i j k - g i j k))
    in
      !p : num.
        prime p
        ==>
        ?L : (int # (int # int)) list.
          poly_cong p (determinant p) (product_of_linear_forms L)``;
