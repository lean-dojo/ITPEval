(* Statement-only formalization of PutnamBench corpus artifact putnam_2001_b1:
   balanced two-colorings of an even square grid give equal sums of the
   row-major integer labels in the two colors; this file contains no proof. *)

From Stdlib Require Import Arith ZArith.

Inductive putnam_2001_b1_color : Type :=
| putnam_2001_b1_red
| putnam_2001_b1_black.

Fixpoint putnam_2001_b1_nat_sum
    (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O => O
  | S k => Nat.add (putnam_2001_b1_nat_sum k f) (f k)
  end.

Fixpoint putnam_2001_b1_Z_sum
    (n : nat) (f : nat -> Z) : Z :=
  match n with
  | O => 0%Z
  | S k => Z.add (putnam_2001_b1_Z_sum k f) (f k)
  end.

Theorem putnam_2001_b1
    (n : nat)
    (nums : nat -> nat -> Z)
    (colors : nat -> nat -> putnam_2001_b1_color)
    (hn : Nat.lt 0 n)
    (heven : exists m : nat, n = Nat.mul 2 m)
    (hnums :
      forall i j : nat,
        Nat.lt i n ->
        Nat.lt j n ->
        nums i j =
          Z.of_nat (Nat.add (Nat.add (Nat.mul i n) j) 1))
    (hcolorsrows :
      forall i : nat,
        Nat.lt i n ->
        putnam_2001_b1_nat_sum n
          (fun j : nat =>
             match colors i j with
             | putnam_2001_b1_red => 1
             | putnam_2001_b1_black => 0
             end) =
        Nat.div n 2)
    (hcolorscols :
      forall j : nat,
        Nat.lt j n ->
        putnam_2001_b1_nat_sum n
          (fun i : nat =>
             match colors i j with
             | putnam_2001_b1_red => 1
             | putnam_2001_b1_black => 0
             end) =
        Nat.div n 2) :
  putnam_2001_b1_Z_sum n
    (fun i : nat =>
       putnam_2001_b1_Z_sum n
         (fun j : nat =>
            match colors i j with
            | putnam_2001_b1_red => nums i j
            | putnam_2001_b1_black => 0%Z
            end)) =
  putnam_2001_b1_Z_sum n
    (fun i : nat =>
       putnam_2001_b1_Z_sum n
         (fun j : nat =>
            match colors i j with
            | putnam_2001_b1_red => 0%Z
            | putnam_2001_b1_black => nums i j
            end)).
Admitted.
