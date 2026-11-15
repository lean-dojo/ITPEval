(*
  Statement-only formalization of the Babel-formal artifact group: group laws,
  commutative multiplication, group actions, orbits, and stabilizers. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val babel_group_def = new_definition (
  "babel_group_def",
  ``babel_group (mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a) <=>
      (!a b c. mul a (mul b c) = mul (mul a b) c) /\
      (!a. mul a e = a) /\
      (!a. mul e a = a) /\
      (!a. mul (ginv a) a = e) /\
      (!a. mul a (ginv a) = e)``);

val babel_group_comm_def = new_definition (
  "babel_group_comm_def",
  ``babel_group_comm (mul : 'a -> 'a -> 'a) (e : 'a)
                     (ginv : 'a -> 'a) <=>
      babel_group mul e ginv /\
      (!a b. mul a b = mul b a)``);

val mul_rotate_prime =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a).
      babel_group_comm mul e ginv ==>
      !a b c. mul a (mul b c) = mul b (mul c a)``;

val mul_left_cancel =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a).
      babel_group mul e ginv ==>
      !a b c. mul a b = mul a c ==> b = c``;

val mul_right_cancel =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a).
      babel_group mul e ginv ==>
      !a b c. mul b a = mul c a ==> b = c``;

val inv_inv =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a).
      babel_group mul e ginv ==>
      !a. ginv (ginv a) = a``;

val inv_mul =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a).
      babel_group mul e ginv ==>
      !a b. ginv (mul a b) = mul (ginv b) (ginv a)``;

val inv_eq_of_mul_eq_one =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a).
      babel_group mul e ginv ==>
      !a b. mul a b = e ==> b = ginv a``;

val babel_group_action_def = new_definition (
  "babel_group_action_def",
  ``babel_group_action (mul : 'a -> 'a -> 'a) (e : 'a)
                      (ginv : 'a -> 'a) (act : 'a -> 'b -> 'b) <=>
      babel_group mul e ginv /\
      (!x. act e x = x) /\
      (!g h x. act (mul g h) x = act g (act h x))``);

val act_inv =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !g x. act (ginv g) (act g x) = x``;

val act_inv_r =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !g x. act g (act (ginv g) x) = x``;

val babel_orbit_def = new_definition (
  "babel_orbit_def",
  ``babel_orbit (act : 'a -> 'b -> 'b) x y <=>
      ?g. act g x = y``);

val babel_stabilizer_def = new_definition (
  "babel_stabilizer_def",
  ``babel_stabilizer (act : 'a -> 'b -> 'b) x g <=>
      act g x = x``);

val orbit_refl =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x. babel_orbit act x x``;

val orbit_sym =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x y. babel_orbit act x y ==> babel_orbit act y x``;

val orbit_trans =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x y z.
        babel_orbit act x y ==>
        babel_orbit act y z ==>
        babel_orbit act x z``;

val orbit_partition =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x y z.
        babel_orbit act x y ==>
        (babel_orbit act x z <=> babel_orbit act y z)``;

val stabilizer_mul =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x g h.
        babel_stabilizer act x g ==>
        babel_stabilizer act x h ==>
        babel_stabilizer act x (mul g h)``;

val stabilizer_inv =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x g.
        babel_stabilizer act x g ==>
        babel_stabilizer act x (ginv g)``;

val stabilizer_one =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x. babel_stabilizer act x e``;

val stabilizer_conjugate =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x g h.
        babel_stabilizer act x h ==>
        babel_stabilizer act (act g x)
          (mul (mul g h) (ginv g))``;

val stabilizer_conjugate_orbit =
  ``!(mul : 'a -> 'a -> 'a) (e : 'a) (ginv : 'a -> 'a)
      (act : 'a -> 'b -> 'b).
      babel_group_action mul e ginv act ==>
      !x y g.
        act g x = y ==>
        !h. (babel_stabilizer act y h <=>
             babel_stabilizer act x
               (mul (mul (ginv g) h) g))``;
