(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1148215 (thousand-theorems__hol4__Q1148215), "Mitchell's embedding
  theorem": every abelian category admits a full and faithful functor into
  modules over some ring that preserves finite limits and finite colimits.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q1148215_category_def = new_definition (
  "q1148215_category_def",
  ``q1148215_category
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (id : 'o -> 'm) (comp : 'm -> 'm -> 'm) <=>
      (!f. f IN morphisms ==> dom f IN objects /\ cod f IN objects) /\
      (!x. x IN objects ==>
        id x IN morphisms /\ dom (id x) = x /\ cod (id x) = x) /\
      (!f g.
        f IN morphisms /\ g IN morphisms /\ cod f = dom g
        ==>
        comp g f IN morphisms /\
        dom (comp g f) = dom f /\
        cod (comp g f) = cod g) /\
      (!f. f IN morphisms ==>
        comp f (id (dom f)) = f /\
        comp (id (cod f)) f = f) /\
      (!f g h.
        f IN morphisms /\ g IN morphisms /\ h IN morphisms /\
        cod f = dom g /\ cod g = dom h
        ==>
        comp h (comp g f) = comp (comp h g) f)``);

val q1148215_preadditive_def = new_definition (
  "q1148215_preadditive_def",
  ``q1148215_preadditive
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (comp : 'm -> 'm -> 'm)
      (zero : 'o -> 'o -> 'm)
      (add : 'm -> 'm -> 'm) (neg : 'm -> 'm) <=>
      (!x y.
        x IN objects /\ y IN objects
        ==>
        zero x y IN morphisms /\
        dom (zero x y) = x /\ cod (zero x y) = y) /\
      (!f g.
        f IN morphisms /\ g IN morphisms /\
        dom f = dom g /\ cod f = cod g
        ==>
        add f g IN morphisms /\
        dom (add f g) = dom f /\ cod (add f g) = cod f) /\
      (!f. f IN morphisms ==>
        neg f IN morphisms /\
        dom (neg f) = dom f /\ cod (neg f) = cod f) /\
      (!f. f IN morphisms ==>
        add (zero (dom f) (cod f)) f = f /\
        add (neg f) f = zero (dom f) (cod f)) /\
      (!f g.
        f IN morphisms /\ g IN morphisms /\
        dom f = dom g /\ cod f = cod g
        ==>
        add f g = add g f) /\
      (!f g h.
        f IN morphisms /\ g IN morphisms /\ h IN morphisms /\
        dom f = dom g /\ cod f = cod g /\
        dom g = dom h /\ cod g = cod h
        ==>
        add (add f g) h = add f (add g h)) /\
      (!f g h.
        f IN morphisms /\ g IN morphisms /\ h IN morphisms /\
        dom f = dom g /\ cod f = cod g /\ cod f = dom h
        ==>
        comp h (add f g) = add (comp h f) (comp h g)) /\
      (!f g h.
        f IN morphisms /\ g IN morphisms /\ h IN morphisms /\
        cod f = dom g /\ dom g = dom h /\ cod g = cod h
        ==>
        comp (add g h) f = add (comp g f) (comp h f))``);

val q1148215_zero_object_def = new_definition (
  "q1148215_zero_object_def",
  ``q1148215_zero_object
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o) (z : 'o) <=>
      z IN objects /\
      (!x. x IN objects ==>
        ?f. f IN morphisms /\ dom f = z /\ cod f = x /\
            !g. g IN morphisms /\ dom g = z /\ cod g = x ==> g = f) /\
      (!x. x IN objects ==>
        ?f. f IN morphisms /\ dom f = x /\ cod f = z /\
            !g. g IN morphisms /\ dom g = x /\ cod g = z ==> g = f)``);

val q1148215_biproduct_def = new_definition (
  "q1148215_biproduct_def",
  ``q1148215_biproduct
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (id : 'o -> 'm) (comp : 'm -> 'm -> 'm)
      (zero : 'o -> 'o -> 'm) (add : 'm -> 'm -> 'm)
      (x : 'o) (y : 'o) (b : 'o)
      (i1 : 'm) (i2 : 'm) (p1 : 'm) (p2 : 'm) <=>
      b IN objects /\
      i1 IN morphisms /\ dom i1 = x /\ cod i1 = b /\
      i2 IN morphisms /\ dom i2 = y /\ cod i2 = b /\
      p1 IN morphisms /\ dom p1 = b /\ cod p1 = x /\
      p2 IN morphisms /\ dom p2 = b /\ cod p2 = y /\
      comp p1 i1 = id x /\
      comp p2 i2 = id y /\
      comp p1 i2 = zero y x /\
      comp p2 i1 = zero x y /\
      add (comp i1 p1) (comp i2 p2) = id b``);

val q1148215_kernel_def = new_definition (
  "q1148215_kernel_def",
  ``q1148215_kernel
      (morphisms : 'm set) (dom : 'm -> 'o) (cod : 'm -> 'o)
      (comp : 'm -> 'm -> 'm) (zero : 'o -> 'o -> 'm)
      (k : 'm) (f : 'm) <=>
      k IN morphisms /\ f IN morphisms /\ cod k = dom f /\
      comp f k = zero (dom k) (cod f) /\
      !h. h IN morphisms /\ cod h = dom f /\
          comp f h = zero (dom h) (cod f)
          ==>
          ?u. u IN morphisms /\ dom u = dom h /\ cod u = dom k /\
              comp k u = h /\
              !v. v IN morphisms /\ dom v = dom h /\ cod v = dom k /\
                  comp k v = h ==> v = u``);

val q1148215_cokernel_def = new_definition (
  "q1148215_cokernel_def",
  ``q1148215_cokernel
      (morphisms : 'm set) (dom : 'm -> 'o) (cod : 'm -> 'o)
      (comp : 'm -> 'm -> 'm) (zero : 'o -> 'o -> 'm)
      (f : 'm) (q : 'm) <=>
      f IN morphisms /\ q IN morphisms /\ cod f = dom q /\
      comp q f = zero (dom f) (cod q) /\
      !h. h IN morphisms /\ dom h = cod f /\
          comp h f = zero (dom f) (cod h)
          ==>
          ?u. u IN morphisms /\ dom u = cod q /\ cod u = cod h /\
              comp u q = h /\
              !v. v IN morphisms /\ dom v = cod q /\ cod v = cod h /\
                  comp v q = h ==> v = u``);

val q1148215_monomorphism_def = new_definition (
  "q1148215_monomorphism_def",
  ``q1148215_monomorphism
      (morphisms : 'm set) (dom : 'm -> 'o) (cod : 'm -> 'o)
      (comp : 'm -> 'm -> 'm) (f : 'm) <=>
      f IN morphisms /\
      !g h. g IN morphisms /\ h IN morphisms /\
            cod g = dom f /\ cod h = dom f /\ dom g = dom h /\
            comp f g = comp f h
            ==> g = h``);

val q1148215_epimorphism_def = new_definition (
  "q1148215_epimorphism_def",
  ``q1148215_epimorphism
      (morphisms : 'm set) (dom : 'm -> 'o) (cod : 'm -> 'o)
      (comp : 'm -> 'm -> 'm) (f : 'm) <=>
      f IN morphisms /\
      !g h. g IN morphisms /\ h IN morphisms /\
            dom g = cod f /\ dom h = cod f /\ cod g = cod h /\
            comp g f = comp h f
            ==> g = h``);

val q1148215_abelian_category_def = new_definition (
  "q1148215_abelian_category_def",
  ``q1148215_abelian_category
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (id : 'o -> 'm) (comp : 'm -> 'm -> 'm)
      (zero : 'o -> 'o -> 'm)
      (add : 'm -> 'm -> 'm) (neg : 'm -> 'm) <=>
      q1148215_category objects morphisms dom cod id comp /\
      q1148215_preadditive objects morphisms dom cod comp zero add neg /\
      (?z. q1148215_zero_object objects morphisms dom cod z) /\
      (!x y. x IN objects /\ y IN objects ==>
        ?b i1 i2 p1 p2.
          q1148215_biproduct objects morphisms dom cod id comp zero add
            x y b i1 i2 p1 p2) /\
      (!f. f IN morphisms ==>
        ?k. q1148215_kernel morphisms dom cod comp zero k f) /\
      (!f. f IN morphisms ==>
        ?q. q1148215_cokernel morphisms dom cod comp zero f q) /\
      (!f. q1148215_monomorphism morphisms dom cod comp f ==>
        ?g. q1148215_kernel morphisms dom cod comp zero f g) /\
      (!f. q1148215_epimorphism morphisms dom cod comp f ==>
        ?g. q1148215_cokernel morphisms dom cod comp zero g f)``);

val q1148215_ring_def = new_definition (
  "q1148215_ring_def",
  ``q1148215_ring
      (carrier : 'a set) (zero : 'a) (rone_value : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) <=>
      zero IN carrier /\ rone_value IN carrier /\
      (!x y. x IN carrier /\ y IN carrier ==>
        add x y IN carrier /\ mul x y IN carrier) /\
      (!x. x IN carrier ==> neg x IN carrier) /\
      (!x. x IN carrier ==>
        add zero x = x /\ add (neg x) x = zero /\
        mul rone_value x = x /\ mul x rone_value = x) /\
      (!x y. x IN carrier /\ y IN carrier ==> add x y = add y x) /\
      (!x y z. x IN carrier /\ y IN carrier /\ z IN carrier ==>
        add (add x y) z = add x (add y z) /\
        mul (mul x y) z = mul x (mul y z) /\
        mul x (add y z) = add (mul x y) (mul x z) /\
        mul (add x y) z = add (mul x z) (mul y z))``);

val q1148215_module_def = new_definition (
  "q1148215_module_def",
  ``q1148215_module
      (rcarrier : 'r set) (rzero : 'r) (rone : 'r)
      (radd : 'r -> 'r -> 'r) (rmul : 'r -> 'r -> 'r)
      (mcarrier : 'a set) (mzero : 'a)
      (madd : 'a -> 'a -> 'a) (mneg : 'a -> 'a)
      (smul : 'r -> 'a -> 'a) <=>
      mzero IN mcarrier /\
      (!x y. x IN mcarrier /\ y IN mcarrier ==> madd x y IN mcarrier) /\
      (!x. x IN mcarrier ==> mneg x IN mcarrier) /\
      (!r x. r IN rcarrier /\ x IN mcarrier ==> smul r x IN mcarrier) /\
      (!x. x IN mcarrier ==>
        madd mzero x = x /\ madd (mneg x) x = mzero) /\
      (!x y. x IN mcarrier /\ y IN mcarrier ==> madd x y = madd y x) /\
      (!x y z. x IN mcarrier /\ y IN mcarrier /\ z IN mcarrier ==>
        madd (madd x y) z = madd x (madd y z)) /\
      (!x. x IN mcarrier ==>
        smul rone x = x /\ smul rzero x = mzero) /\
      (!r s x. r IN rcarrier /\ s IN rcarrier /\ x IN mcarrier ==>
        smul (radd r s) x = madd (smul r x) (smul s x) /\
        smul (rmul r s) x = smul r (smul s x)) /\
      (!r x y. r IN rcarrier /\ x IN mcarrier /\ y IN mcarrier ==>
        smul r (madd x y) = madd (smul r x) (smul r y))``);

val q1148215_linear_def = new_definition (
  "q1148215_linear_def",
  ``q1148215_linear
      (rcarrier : 'r set) (mcarrier : 'o -> 'a set)
      (mzero : 'o -> 'a) (madd : 'o -> 'a -> 'a -> 'a)
      (smul : 'o -> 'r -> 'a -> 'a)
      (x : 'o) (y : 'o) (f : 'a -> 'a) <=>
      (!a. a IN mcarrier x ==> f a IN mcarrier y) /\
      f (mzero x) = mzero y /\
      (!a b. a IN mcarrier x /\ b IN mcarrier x ==>
        f (madd x a b) = madd y (f a) (f b)) /\
      (!r a. r IN rcarrier /\ a IN mcarrier x ==>
        f (smul x r a) = smul y r (f a))``);

(*
  HOL cannot existentially quantify over carrier types. Let kappa bound the
  object and arrow carriers and num. The standard small-category construction
  admits ring codes in a powerset of kappa; a further powerset is sufficient
  for all module carriers. The types below retain that carrier freedom instead
  of identifying ring elements and module vectors.
*)
val freyd_mitchell =
  ``!(objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (id : 'o -> 'm) (comp : 'm -> 'm -> 'm)
      (zero : 'o -> 'o -> 'm)
      (add : 'm -> 'm -> 'm) (neg : 'm -> 'm).
      q1148215_abelian_category
        objects morphisms dom cod id comp zero add neg
      ==>
      ?(rcarrier : (('o # 'm # num) set) set)
       (rzero : ('o # 'm # num) set)
       (rone : ('o # 'm # num) set)
       (radd : ('o # 'm # num) set ->
               ('o # 'm # num) set -> ('o # 'm # num) set)
       (rmul : ('o # 'm # num) set ->
               ('o # 'm # num) set -> ('o # 'm # num) set)
       (rneg : ('o # 'm # num) set -> ('o # 'm # num) set)
       (mcarrier : 'o -> ((('o # 'm # num) set) set) set)
       (mzero : 'o -> (('o # 'm # num) set) set)
       (madd : 'o -> (('o # 'm # num) set) set ->
               (('o # 'm # num) set) set ->
               (('o # 'm # num) set) set)
       (mneg : 'o -> (('o # 'm # num) set) set ->
               (('o # 'm # num) set) set)
       (smul : 'o -> ('o # 'm # num) set ->
               (('o # 'm # num) set) set ->
               (('o # 'm # num) set) set)
       (fmap : 'm -> (('o # 'm # num) set) set ->
               (('o # 'm # num) set) set).
        q1148215_ring rcarrier rzero rone radd rmul rneg /\
        (!x. x IN objects ==>
          q1148215_module rcarrier rzero rone radd rmul
            (mcarrier x) (mzero x) (madd x) (mneg x) (smul x)) /\
        (!f. f IN morphisms ==>
          q1148215_linear rcarrier mcarrier mzero madd smul
            (dom f) (cod f) (fmap f)) /\
        (!x a. x IN objects /\ a IN mcarrier x ==>
          fmap (id x) a = a) /\
        (!f g a.
          f IN morphisms /\ g IN morphisms /\ cod f = dom g /\
          a IN mcarrier (dom f)
          ==>
          fmap (comp g f) a = fmap g (fmap f a)) /\
        (!x y h.
          x IN objects /\ y IN objects /\
          q1148215_linear rcarrier mcarrier mzero madd smul x y h
          ==>
          ?f. f IN morphisms /\ dom f = x /\ cod f = y /\
              !a. a IN mcarrier x ==> fmap f a = h a) /\
        (!f g.
          f IN morphisms /\ g IN morphisms /\
          dom f = dom g /\ cod f = cod g /\
          (!a. a IN mcarrier (dom f) ==> fmap f a = fmap g a)
          ==>
          f = g) /\
        (!x y a.
          x IN objects /\ y IN objects /\ a IN mcarrier x
          ==>
          fmap (zero x y) a = mzero y) /\
        (!f g a.
          f IN morphisms /\ g IN morphisms /\
          dom f = dom g /\ cod f = cod g /\
          a IN mcarrier (dom f)
          ==>
          fmap (add f g) a = madd (cod f) (fmap f a) (fmap g a)) /\
        (!k f.
          q1148215_kernel morphisms dom cod comp zero k f
          ==>
          (!a b. a IN mcarrier (dom k) /\ b IN mcarrier (dom k) /\
                 fmap k a = fmap k b ==> a = b) /\
          (!x. x IN mcarrier (dom f) ==>
            (fmap f x = mzero (cod f) <=>
             ?a. a IN mcarrier (dom k) /\ fmap k a = x))) /\
        (!f q.
          q1148215_cokernel morphisms dom cod comp zero f q
          ==>
          (!y. y IN mcarrier (cod q) ==>
            ?x. x IN mcarrier (dom q) /\ fmap q x = y) /\
          (!x. x IN mcarrier (dom q) ==>
            (fmap q x = mzero (cod q) <=>
             ?a. a IN mcarrier (dom f) /\ fmap f a = x)))``;
