(*
  Statement-only formalization of "The Four Color Problem" from Hundred Theorems item 032. This
  file contains no proof.
*)

(*
  Hundred Theorems item 032, "The Four Color Problem": every simple map of
  open connected regions over an arbitrary modeled real plane is colorable
  with at most four colors, with adjacent regions separated. This is a
  statement-only formalization and contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory;

val the_four_color_problem =
  ``!(le : 'r -> 'r -> bool)
      (supremum : ('r -> bool) -> 'r)
      (add : 'r -> 'r -> 'r)
      (zero : 'r)
      (neg : 'r -> 'r)
      (mul : 'r -> 'r -> 'r)
      (one : 'r)
      (inv : 'r -> 'r).
      let real_eq =
        \x y. le x y /\ le y x
      in
      let upper_bounds =
        \(s : 'r -> bool) z. !y. s y ==> le y z
      in
      let downward_closure =
        \(s : 'r -> bool) x. ?y. s y /\ le x y
      in
      let nonempty =
        \(s : 'r -> bool). ?x. s x
      in
      let has_upper_bound =
        \(s : 'r -> bool). ?z. upper_bounds s z
      in
      let has_supremum =
        \(s : 'r -> bool). nonempty s /\ has_upper_bound s
      in
      let real_model =
        ((!x. le x x) /\
         (!x y z. le x y /\ le y z ==> le x z) /\
         (!s. has_supremum s ==> upper_bounds s (supremum s)) /\
         (!s x.
            has_supremum s ==>
            downward_closure s x \/ le (supremum s) x) /\
         (!x y z. le y z ==> le (add x y) (add x z)) /\
         (!x y. real_eq (add x y) (add y x)) /\
         (!x y z. real_eq (add x (add y z)) (add (add x y) z)) /\
         (!x. real_eq (add zero x) x) /\
         (!x. real_eq (add x (neg x)) zero) /\
         (!x y z.
            le zero x /\ le y z ==>
            le (mul x y) (mul x z)) /\
         (!x y. real_eq (mul x y) (mul y x)) /\
         (!x y z. real_eq (mul x (mul y z)) (mul (mul x y) z)) /\
         (!x y z.
            real_eq (mul x (add y z))
                    (add (mul x y) (mul x z))) /\
         (!x. real_eq (mul one x) x) /\
         (!x. ~real_eq x zero ==> real_eq (mul x (inv x)) one) /\
         ~real_eq one zero)
      in
      let subregion =
        \(r1 : ('r # 'r) -> bool) r2.
          !p. r1 p ==> r2 p
      in
      let meet =
        \(r1 : ('r # 'r) -> bool) r2.
          ?p. r1 p /\ r2 p
      in
      let in_interval =
        \left right t. ~(le t left) /\ ~(le right t)
      in
      let open_region =
        \(r : ('r # 'r) -> bool).
          !p.
            r p ==>
            ?left right bottom top.
              in_interval left right (FST p) /\
              in_interval bottom top (SND p) /\
              (!q.
                 in_interval left right (FST q) /\
                 in_interval bottom top (SND q) ==>
                 r q)
      in
      let connected =
        \(r : ('r # 'r) -> bool).
          !u v.
            open_region u /\
            open_region v /\
            subregion r (\p. u p \/ v p) /\
            meet u r /\
            meet v r ==>
            meet u v
      in
      let plain_map =
        \(m : ('r # 'r) -> ('r # 'r) -> bool).
          (!p q. m p q ==> m q p) /\
          (!p q r. m p q /\ m q r ==> m p r)
      in
      let cover =
        \(m : ('r # 'r) -> ('r # 'r) -> bool) p.
          m p p
      in
      let submap =
        \(m1 : ('r # 'r) -> ('r # 'r) -> bool) m2.
          !p. subregion (m1 p) (m2 p)
      in
      let at_most_regions =
        \(n : num) (m : ('r # 'r) -> ('r # 'r) -> bool).
          ?representatives : num -> ('r # 'r).
            !p.
              cover m p ==>
              ?i. i < n /\ m (representatives i) p
      in
      let simple_map =
        \(m : ('r # 'r) -> ('r # 'r) -> bool).
          plain_map m /\
          (!p. open_region (m p)) /\
          (!p. connected (m p))
      in
      let finite_simple_map =
        \(m : ('r # 'r) -> ('r # 'r) -> bool).
          simple_map m /\ ?n. at_most_regions n m
      in
      let closure =
        \(r : ('r # 'r) -> bool) p.
          !u. open_region u /\ u p ==> meet r u
      in
      let border =
        \(m : ('r # 'r) -> ('r # 'r) -> bool) p q x.
          closure (m p) x /\ closure (m q) x
      in
      let corner_map =
        \(m : ('r # 'r) -> ('r # 'r) -> bool) p q r.
          m q r /\ closure (m q) p
      in
      let not_corner =
        \(m : ('r # 'r) -> ('r # 'r) -> bool) p.
          at_most_regions 2 (corner_map m p)
      in
      let adjacent =
        \(m : ('r # 'r) -> ('r # 'r) -> bool) p q.
          ~(m p q) /\ meet (not_corner m) (border m p q)
      in
      let coloring =
        \(m : ('r # 'r) -> ('r # 'r) -> bool) k.
          plain_map k /\
          subregion (cover k) (cover m) /\
          submap m k /\
          (!p q. adjacent m p q ==> ~(k p q))
      in
      let colorable_with =
        \(n : num) (m : ('r # 'r) -> ('r # 'r) -> bool).
          ?k. coloring m k /\ at_most_regions n k
      in
        real_model ==>
        !m : ('r # 'r) -> ('r # 'r) -> bool.
          (finite_simple_map m ==> colorable_with 4 m) /\
          (simple_map m ==> colorable_with 4 m)``;
