(* Statement-only formalization over an arbitrary group. *)

Record putnam_1997_a4_group (G : Type) : Type := {
  putnam_1997_a4_mul : G -> G -> G;
  putnam_1997_a4_one : G;
  putnam_1997_a4_inv : G -> G;
  putnam_1997_a4_assoc :
    forall x y z : G,
      putnam_1997_a4_mul x (putnam_1997_a4_mul y z) =
      putnam_1997_a4_mul (putnam_1997_a4_mul x y) z;
  putnam_1997_a4_left_identity :
    forall x : G, putnam_1997_a4_mul putnam_1997_a4_one x = x;
  putnam_1997_a4_right_identity :
    forall x : G, putnam_1997_a4_mul x putnam_1997_a4_one = x;
  putnam_1997_a4_left_inverse :
    forall x : G,
      putnam_1997_a4_mul (putnam_1997_a4_inv x) x =
      putnam_1997_a4_one;
  putnam_1997_a4_right_inverse :
    forall x : G,
      putnam_1997_a4_mul x (putnam_1997_a4_inv x) =
      putnam_1997_a4_one
}.

Arguments putnam_1997_a4_mul {G} _ _ _.
Arguments putnam_1997_a4_one {G} _.

Theorem putnam_1997_a4
    (G : Type)
    (grp : putnam_1997_a4_group G)
    (f : G -> G)
    (hf : forall g1 g2 g3 h1 h2 h3 : G,
      (putnam_1997_a4_mul grp
         (putnam_1997_a4_mul grp g1 g2) g3 =
         putnam_1997_a4_one grp /\
       putnam_1997_a4_mul grp
         (putnam_1997_a4_mul grp h1 h2) h3 =
         putnam_1997_a4_one grp) ->
      putnam_1997_a4_mul grp
        (putnam_1997_a4_mul grp (f g1) (f g2)) (f g3) =
      putnam_1997_a4_mul grp
        (putnam_1997_a4_mul grp (f h1) (f h2)) (f h3)) :
  exists a : G,
    let psi := fun g => putnam_1997_a4_mul grp a (f g) in
    forall x y : G,
      psi (putnam_1997_a4_mul grp x y) =
      putnam_1997_a4_mul grp (psi x) (psi y).
Admitted.
