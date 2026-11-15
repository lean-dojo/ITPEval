(*
  Statement-only formalization of the Babel-formal topic circle_average. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val is_add_monoid_def = new_definition (
  "is_add_monoid_def",
  ``is_add_monoid (zero : 'a) (add : 'a -> 'a -> 'a) <=>
      (!x. add x zero = x) /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z))``);

val is_integral_def = new_definition (
  "is_integral_def",
  ``is_integral (integral : ('a -> 'a) -> 'a)
                 (add : 'a -> 'a -> 'a) (zero : 'a) <=>
      (!g h. (!t. g t = h t) ==> integral g = integral h) /\
      (!c. integral (\t. c) = c) /\
      (!f g. integral (\t. add (f t) (g t)) =
             add (integral f) (integral g)) /\
      (!f c. integral (\t. f (add t c)) = integral f)``);

val circleMap_def = new_definition (
  "circleMap_def",
  ``circleMap (add : 'a -> 'a -> 'a) c t = add t c``);

val circleAverage_def = new_definition (
  "circleAverage_def",
  ``circleAverage (integral : ('a -> 'a) -> 'a)
                   (add : 'a -> 'a -> 'a) (f : 'a -> 'a) c =
      integral (\t. f (circleMap add c t))``);

val circleMap_zero =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a).
      is_add_monoid zero add ==>
      !t. circleMap add zero t = t``;

val circleAverage_zero =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !f. circleAverage integral add f zero = integral f``;

val circleAverage_add =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) g c.
        circleAverage integral add (\z. add (f z) (g z)) c =
        add (circleAverage integral add f c)
            (circleAverage integral add g c)``;

val circleAverage_fun_add =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c.
        circleAverage integral add (\z. f (add z c)) zero =
        circleAverage integral add f c``;

val circleMap_add =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a).
      is_add_monoid zero add ==>
      !c d t.
        circleMap add (add c d) t =
        circleMap add c (circleMap add d t)``;

val circleAverage_shift =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c d.
        circleAverage integral add f (add c d) =
        circleAverage integral add (\z. f (add z d)) c``;

val circleAverage_const =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !k c. circleAverage integral add (\z. k) c = k``;

val circleAverage_add_const =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) k c.
        circleAverage integral add (\z. add (f z) k) c =
        add (circleAverage integral add f c) k``;

val circleAverage_comm_add =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) g c.
        circleAverage integral add (\z. add (f z) (g z)) c =
        circleAverage integral add (\z. add (g z) (f z)) c``;

val circleAverage_add_assoc =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) g h c.
        circleAverage integral add
          (\z. add (add (f z) (g z)) (h z)) c =
        add (circleAverage integral add f c)
            (add (circleAverage integral add g c)
                 (circleAverage integral add h c))``;

val circleAverage_center_comm =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c d.
        circleAverage integral add f (add c d) =
        circleAverage integral add f (add d c)``;

val circleAverage_center_independent =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c.
        circleAverage integral add f c = integral f``;

val circleAverage_center_eq =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c d.
        circleAverage integral add f c =
        circleAverage integral add f d``;

val circleAverage_idempotent =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c.
        circleAverage integral add
          (\z. circleAverage integral add f z) c =
        circleAverage integral add f c``;

val circleAverage_of_zero_integral =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c.
        integral f = zero ==>
        circleAverage integral add f c = zero``;

val circleAverage_linear =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) g c.
        circleAverage integral add (\z. add (f z) (g z)) c =
        add (circleAverage integral add f c)
            (circleAverage integral add g c)``;

val circleAverage_shift_commute =
  ``!(zero : 'a) (add : 'a -> 'a -> 'a)
      (integral : ('a -> 'a) -> 'a).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f : 'a -> 'a) c d.
        circleAverage integral add
          (\z. f (circleMap add d z)) c =
        circleAverage integral add f (add c d)``;
