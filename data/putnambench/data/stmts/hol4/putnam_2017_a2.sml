(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a2:
  recursively defined rational functions are integer-coefficient polynomials
  at every positive index. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory ratTheory;

val putnam_2017_a2 =
  ``let finite_poly =
      \p : num -> rat. FINITE {k : num | p k <> 0};
      int_poly =
        \p : num -> int. FINITE {k : num | p k <> 0};
      poly_zero =
        (\k : num. (0 : rat));
      poly_one =
        (\k : num. if k = 0 then (1 : rat) else 0);
      poly_X =
        (\k : num. if k = 1 then (1 : rat) else 0);
      poly_add =
        (\p q : num -> rat.
           \k : num. p k + q k);
      poly_neg =
        (\p : num -> rat.
           \k : num. -(p k));
      poly_mul =
        (\p q : num -> rat.
           \k : num.
             ITSET
               (\i : num. \acc : rat. p i * q (k - i) + acc)
               (count (k + 1))
               0q);
      poly_sub =
        (\p q : num -> rat.
           poly_add p (poly_neg q));
      ratfunc_valid =
        (\r : (num -> rat) # (num -> rat).
           finite_poly (FST r) /\
           finite_poly (SND r) /\
           SND r <> poly_zero);
      ratfunc_eq =
        (\r s : (num -> rat) # (num -> rat).
           ratfunc_valid r /\
           ratfunc_valid s /\
           poly_mul (FST r) (SND s) =
             poly_mul (FST s) (SND r));
      ratfunc_zero =
        (poly_zero, poly_one);
      ratfunc_one =
        (poly_one, poly_one);
      ratfunc_X =
        (poly_X, poly_one);
      ratfunc_mul =
        (\r s : (num -> rat) # (num -> rat).
           (poly_mul (FST r) (FST s),
            poly_mul (SND r) (SND s)));
      ratfunc_sub =
        (\r s : (num -> rat) # (num -> rat).
           (poly_sub
              (poly_mul (FST r) (SND s))
              (poly_mul (FST s) (SND r)),
            poly_mul (SND r) (SND s)));
      ratfunc_inv =
        (\r : (num -> rat) # (num -> rat).
           if FST r = poly_zero
           then ratfunc_zero
           else (SND r, FST r));
      ratfunc_div =
        (\r s : (num -> rat) # (num -> rat).
           ratfunc_mul r (ratfunc_inv s));
      lift_int_poly =
        (\p : num -> int.
           \k : num. rat_of_int (p k))
    in
      !Q : num -> ((num -> rat) # (num -> rat)).
        (!n : num. ratfunc_valid (Q n)) /\
        ratfunc_eq (Q 0) ratfunc_one /\
        ratfunc_eq (Q 1) ratfunc_X /\
        (!n : num.
           ratfunc_eq
             (Q (n + 2))
             (ratfunc_div
                (ratfunc_sub
                   (ratfunc_mul (Q (n + 1)) (Q (n + 1)))
                   ratfunc_one)
                (Q n)))
        ==>
        !n : num.
          0 < n
          ==>
          ?P : num -> int.
            int_poly P /\
            ratfunc_eq (Q n) (lift_int_poly P, poly_one)``;
