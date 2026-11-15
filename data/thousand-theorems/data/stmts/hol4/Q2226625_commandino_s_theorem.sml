(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2226625 (thousand-theorems__hol4__Q2226625), "Commandino's theorem":
  in an arbitrary characteristic-zero division-ring affine space, a simplex
  centroid divides each median in the dimension-to-one ratio. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val commandinos_theorem =
  ``!(kzero : 'k)
      (kone : 'k)
      (kadd : 'k -> 'k -> 'k)
      (kmul : 'k -> 'k -> 'k)
      (kneg : 'k -> 'k)
      (kinv : 'k -> 'k)
      (vzero : 'v)
      (vadd : 'v -> 'v -> 'v)
      (vneg : 'v -> 'v)
      (smul : 'k -> 'v -> 'v)
      (padd : 'v -> 'p -> 'p)
      (psub : 'p -> 'p -> 'v)
      (n : num)
      (points : num -> 'p)
      (i : num).
      let nat_cast =
        \(m : num).
          ITSET (\j acc. kadd kone acc) {j : num | j < m} kzero
      in
      let scalar_sum =
        \(w : num -> 'k) (s : num set).
          ITSET (\j acc. kadd (w j) acc) s kzero
      in
      let vector_sum =
        \(f : num -> 'v) (s : num set).
          ITSET (\j acc. vadd (f j) acc) s vzero
      in
      let indices = {j : num | j < n + 1}
      in
      let opposite_indices = {j : num | j < n + 1 /\ j <> i}
      in
      let affine_independent =
        !w : num -> 'k.
          scalar_sum w indices = kzero /\
          vector_sum
            (\j. smul (w j) (psub (points j) (points 0)))
            indices = vzero
          ==>
          !j. j IN indices ==> w j = kzero
      in
      let centroid =
        padd
          (smul (kinv (nat_cast (n + 1)))
            (vector_sum
              (\j. psub (points j) (points 0))
              indices))
          (points 0)
      in
      let face_opposite_centroid =
        padd
          (smul (kinv (nat_cast n))
            (vector_sum
              (\j. psub (points j) (points i))
              opposite_indices))
          (points i)
      in
        kone <> kzero /\
        (!a b. kadd a b = kadd b a) /\
        (!a b c. kadd (kadd a b) c = kadd a (kadd b c)) /\
        (!a. kadd kzero a = a) /\
        (!a. kadd (kneg a) a = kzero) /\
        (!a b c. kmul (kmul a b) c = kmul a (kmul b c)) /\
        (!a. kmul kone a = a) /\
        (!a. kmul a kone = a) /\
        (!a b c.
          kmul a (kadd b c) = kadd (kmul a b) (kmul a c)) /\
        (!a b c.
          kmul (kadd a b) c = kadd (kmul a c) (kmul b c)) /\
        kinv kzero = kzero /\
        (!a.
          a <> kzero ==>
          kmul (kinv a) a = kone /\ kmul a (kinv a) = kone) /\
        (!m r. nat_cast m = nat_cast r ==> m = r) /\
        (!x y. vadd x y = vadd y x) /\
        (!x y z. vadd (vadd x y) z = vadd x (vadd y z)) /\
        (!x. vadd vzero x = x) /\
        (!x. vadd (vneg x) x = vzero) /\
        (!x. smul kone x = x) /\
        (!a b x. smul (kmul a b) x = smul a (smul b x)) /\
        (!a b x.
          smul (kadd a b) x = vadd (smul a x) (smul b x)) /\
        (!a x y.
          smul a (vadd x y) = vadd (smul a x) (smul a y)) /\
        (!p. padd vzero p = p) /\
        (!u v p. padd (vadd u v) p = padd u (padd v p)) /\
        (!p q. padd (psub p q) q = p) /\
        (!v p. psub (padd v p) p = v) /\
        n <> 0 /\
        i < n + 1 /\
        affine_independent
        ==>
        psub (points i) centroid =
          smul (nat_cast n)
            (psub centroid face_opposite_centroid)``;
