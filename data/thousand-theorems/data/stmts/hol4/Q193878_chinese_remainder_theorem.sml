(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q193878, "Chinese remainder theorem": for a possibly empty finite
  pairwise-coprime family of ideals in a commutative ring, the quotient by
  their intersection is canonically ring-isomorphic to the product of the
  individual quotients. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q193878_comm_ring_def = new_definition (
  "q193878_comm_ring_def",
  ``q193878_comm_ring
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneR x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z))``);

val q193878_ideal_def = new_definition (
  "q193878_ideal_def",
  ``q193878_ideal
      (zero : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) <=>
      zero IN ideal /\
      (!x y. x IN ideal /\ y IN ideal ==> add x y IN ideal) /\
      (!x. x IN ideal ==> neg x IN ideal) /\
      (!a x. x IN ideal ==> mul a x IN ideal)``);

val q193878_class_def = new_definition (
  "q193878_class_def",
  ``q193878_class
      (add : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) (r : 'r) =
      {x | add x (neg r) IN ideal}``);

val q193878_quotient_carrier_def = new_definition (
  "q193878_quotient_carrier_def",
  ``q193878_quotient_carrier
      (add : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) =
      {cls | ?r. cls = q193878_class add neg ideal r}``);

val q193878_representative_def = new_definition (
  "q193878_representative_def",
  ``q193878_representative
      (add : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) (cls : 'r set) =
      @r. cls = q193878_class add neg ideal r``);

val q193878_quotient_add_def = new_definition (
  "q193878_quotient_add_def",
  ``q193878_quotient_add
      (add : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) (cls1 : 'r set) (cls2 : 'r set) =
      q193878_class add neg ideal
        (add
          (q193878_representative add neg ideal cls1)
          (q193878_representative add neg ideal cls2))``);

val q193878_quotient_mul_def = new_definition (
  "q193878_quotient_mul_def",
  ``q193878_quotient_mul
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (ideal : 'r set)
      (cls1 : 'r set) (cls2 : 'r set) =
      q193878_class add neg ideal
        (mul
          (q193878_representative add neg ideal cls1)
          (q193878_representative add neg ideal cls2))``);

val q193878_quotient_neg_def = new_definition (
  "q193878_quotient_neg_def",
  ``q193878_quotient_neg
      (add : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) (cls : 'r set) =
      q193878_class add neg ideal
        (neg (q193878_representative add neg ideal cls))``);

val quotientInfRingEquivPiQuotient =
  ``!(zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (indices : 'i set) (ideals : 'i -> 'r set).
      q193878_comm_ring zero oneR add mul neg /\
      FINITE indices /\
      (!i.
        i IN indices ==>
        q193878_ideal zero add mul neg (ideals i)) /\
      (!i j.
        i IN indices /\ j IN indices /\ i <> j ==>
        ?a b. a IN ideals i /\ b IN ideals j /\ add a b = oneR)
      ==>
      let infI = {x | !i. i IN indices ==> x IN ideals i} in
      let source = q193878_quotient_carrier add neg infI in
      let target =
        {g : 'i -> 'r set |
          (!i.
            i IN indices ==>
            g i IN q193878_quotient_carrier add neg (ideals i)) /\
          (!i. ~(i IN indices) ==> g i = {})}
      in
      ?e : 'r set -> 'i -> 'r set.
        BIJ e source target /\
        (!r.
          e (q193878_class add neg infI r) =
          (\i.
            if i IN indices
            then q193878_class add neg (ideals i) r
            else {})) /\
        e (q193878_class add neg infI zero) =
          (\i.
            if i IN indices
            then q193878_class add neg (ideals i) zero
            else {}) /\
        e (q193878_class add neg infI oneR) =
          (\i.
            if i IN indices
            then q193878_class add neg (ideals i) oneR
            else {}) /\
        (!cls1 cls2.
          cls1 IN source /\ cls2 IN source ==>
          e (q193878_quotient_add add neg infI cls1 cls2) =
            (\i.
              if i IN indices
              then
                q193878_quotient_add add neg (ideals i)
                  (e cls1 i) (e cls2 i)
              else {})) /\
        (!cls1 cls2.
          cls1 IN source /\ cls2 IN source ==>
          e (q193878_quotient_mul add mul neg infI cls1 cls2) =
            (\i.
              if i IN indices
              then
                q193878_quotient_mul add mul neg (ideals i)
                  (e cls1 i) (e cls2 i)
              else {})) /\
        (!cls.
          cls IN source ==>
          e (q193878_quotient_neg add neg infI cls) =
            (\i.
              if i IN indices
              then q193878_quotient_neg add neg (ideals i) (e cls i)
              else {}))``;
