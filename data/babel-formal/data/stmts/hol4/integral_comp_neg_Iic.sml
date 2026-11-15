(*
  Statement-only formalization of the Babel-formal topic integral_comp_neg_Iic. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val is_integral_context_def = new_definition (
  "is_integral_context_def",
  ``is_integral_context
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (opp : 'r -> 'r)
      (mul : 'r -> 'r -> 'r)
      (le : 'r -> 'r -> bool) (lt : 'r -> 'r -> bool)
      (absR : 'r -> 'r)
      (sigma : ('r -> bool) -> ('r -> 'r) -> 'r) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add (opp x) x = zero) /\
      (!x y z. add x z = add y z ==> x = y) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul x oneR = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x. opp (opp x) = x) /\
      (!x y z. le x y ==> le (add x z) (add y z)) /\
      (!x y z. le zero z ==> le x y ==> le (mul x z) (mul y z)) /\
      le zero oneR /\
      (!x y. le x y \/ le y x) /\
      (!x y. le x y \/ ~(le x y)) /\
      (!x y. le x y ==> le (opp y) (opp x)) /\
      (!x y. le x y ==> le y x ==> x = y) /\
      (!x y. lt x y ==> lt (opp y) (opp x)) /\
      (!x. le x x) /\
      (!x y z. le x y ==> le y z ==> le x z) /\
      (!x y. (lt x y <=> le x y /\ ~(x = y))) /\
      (!x. le zero x ==> absR x = x) /\
      (!x. le x zero ==> absR x = opp x) /\
      (!x. le zero (absR x)) /\
      (!x. absR (opp x) = absR x) /\
      (!x y. le (absR (add x y)) (add (absR x) (absR y))) /\
      (!D f c.
         sigma D (\x. mul c (f x)) = mul c (sigma D f)) /\
      (!D f g.
         (!x. D x ==> f x = g x) ==> sigma D f = sigma D g) /\
      (!D. sigma D (\x. zero) = zero) /\
      (!D f g.
         sigma D (\x. add (f x) (g x)) =
         add (sigma D f) (sigma D g)) /\
      (!D E f.
         (!x. D x ==> E x ==> F) ==>
         sigma (\x. D x \/ E x) f =
         add (sigma D f) (sigma E f)) /\
      (!D f g.
         (!x. D x ==> le (f x) (g x)) ==>
         le (sigma D f) (sigma D g)) /\
      (!D E f.
         (!x. (D x <=> E x)) ==> sigma D f = sigma E f)``);

val iic_def = new_definition (
  "iic_def",
  ``iic (le : 'r -> 'r -> bool) c x <=> le x c``);

val ioi_def = new_definition (
  "ioi_def",
  ``ioi (lt : 'r -> 'r -> bool) c x <=> lt c x``);

val iio_def = new_definition (
  "iio_def",
  ``iio (lt : 'r -> 'r -> bool) c x <=> lt x c``);

val unionD_def = new_definition (
  "unionD_def",
  ``unionD (D : 'r -> bool) E x <=> D x \/ E x``);

val interD_def = new_definition (
  "interD_def",
  ``interD (D : 'r -> bool) E x <=> D x /\ E x``);

val preimage_def = new_definition (
  "preimage_def",
  ``preimage (g : 'r -> 'r) (D : 'r -> bool) x <=> D (g x)``);

val lt_irrefl =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma x.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      ~(lt x x)``;

val lt_trans_strict =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma x y z.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      lt x y ==> lt y z ==> lt x z``;

val preimage_union =
  ``!(D : 'r -> bool) E (g : 'r -> 'r) x.
      (preimage g (unionD D E) x <=>
       preimage g D x \/ preimage g E x)``;

val preimage_inter =
  ``!(D : 'r -> bool) E (g : 'r -> 'r) x.
      (preimage g (interD D E) x <=>
       preimage g D x /\ preimage g E x)``;

val preimage_neg_Ioi =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma c x.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      (preimage opp (ioi lt c) x <=> lt x (opp c))``;

val preimage_neg_Iic =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma c x.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      (preimage opp (iic le c) x <=> iic le x (opp c))``;

val preimage_comp =
  ``!(D : 'r -> bool) (g : 'r -> 'r) h x.
      (preimage g (preimage h D) x <=>
       preimage (\y. h (g y)) D x)``;

val integral_neg =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (f : 'r -> 'r).
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      sigma D (\x. opp (f x)) = opp (sigma D f)``;

val integral_sub =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (f : 'r -> 'r) g.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      sigma D (\x. add (f x) (opp (g x))) =
      add (sigma D f) (opp (sigma D g))``;

val sigma_empty =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma (f : 'r -> 'r).
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      sigma (\x. F) f = zero``;

val sigma_bilinear =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (f : 'r -> 'r) g c d.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      sigma D (\x. add (mul c (f x)) (mul d (g x))) =
      add (mul c (sigma D f)) (mul d (sigma D g))``;

val sigma_le_monotone =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (f : 'r -> 'r) g.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      (!x. D x ==> le (f x) (g x)) ==>
      le (sigma D f) (sigma D g)``;

val sigma_nonneg =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (f : 'r -> 'r).
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      (!x. D x ==> le zero (f x)) ==>
      le zero (sigma D f)``;

val sigma_split =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (P : 'r -> bool) (f : 'r -> 'r).
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      (!x. D x ==> P x \/ ~(P x)) ==>
      sigma D f =
      add (sigma (\x. D x /\ P x) f)
          (sigma (\x. D x /\ ~(P x)) f)``;

val sigma_preimage_neg_Ioi =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (f : 'r -> 'r) c.
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      sigma (preimage opp (ioi lt c)) f =
      sigma (iio lt (opp c)) f``;

val sigma_abs_bound =
  ``!(zero : 'r) oneR add opp mul le lt absR sigma
      (D : 'r -> bool) (f : 'r -> 'r).
      is_integral_context zero oneR add opp mul le lt absR sigma ==>
      le (absR (sigma D f)) (sigma D (\x. absR (f x)))``;

val _ = export_theory();
