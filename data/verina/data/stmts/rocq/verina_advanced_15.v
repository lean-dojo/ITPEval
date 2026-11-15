(* Statement-only formalization of VERINA corpus artifact verina_advanced_15,
   catalog title "increasingTriplet": an executable two-candidate scan for a
   strictly increasing subsequence of length three, together with its
   correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition increasingTriplet_precond (_nums : list Z) : Prop :=
  True.

Fixpoint increasingTriplet_loop
    (xs : list Z)
    (first second : option Z) : bool :=
  match xs with
  | [] => false
  | x :: rest =>
      match first with
      | None =>
          increasingTriplet_loop rest (Some x) None
      | Some f =>
          if Z.leb x f
          then increasingTriplet_loop rest (Some x) second
          else
            match second with
            | None =>
                increasingTriplet_loop rest first (Some x)
            | Some s =>
                if Z.leb x s
                then increasingTriplet_loop rest first (Some x)
                else true
            end
      end
  end.

Definition increasingTriplet
    (nums : list Z)
    (_h_precond : increasingTriplet_precond nums) : bool :=
  if Nat.ltb (length nums) 3%nat
  then false
  else increasingTriplet_loop nums None None.

Fixpoint increasingTriplet_zipIdxFrom
    (nums : list Z)
    (index : nat) : list (Z * nat) :=
  match nums with
  | [] => []
  | x :: rest =>
      (x, index) ::
      increasingTriplet_zipIdxFrom rest (S index)
  end.

Definition increasingTriplet_zipIdx
    (nums : list Z) : list (Z * nat) :=
  increasingTriplet_zipIdxFrom nums 0%nat.

Definition increasingTriplet_hasTriplet
    (nums' : list (Z * nat)) : bool :=
  existsb
    (fun xi =>
      existsb
        (fun yj =>
          existsb
            (fun zk =>
              andb
                (Nat.ltb (snd xi) (snd yj))
                (andb
                  (Nat.ltb (snd yj) (snd zk))
                  (andb
                    (Z.ltb (fst xi) (fst yj))
                    (Z.ltb (fst yj) (fst zk)))))
            nums')
        nums')
    nums'.

Definition increasingTriplet_allNonIncreasing
    (nums' : list (Z * nat)) : bool :=
  forallb
    (fun xi =>
      forallb
        (fun yj =>
          forallb
            (fun zk =>
              orb
                (Nat.leb (snd yj) (snd xi))
                (orb
                  (Nat.leb (snd zk) (snd yj))
                  (orb
                    (Z.leb (fst yj) (fst xi))
                    (Z.leb (fst zk) (fst yj)))))
            nums')
        nums')
    nums'.

Definition increasingTriplet_postcond
    (nums : list Z)
    (result : bool)
    (_h_precond : increasingTriplet_precond nums) : Prop :=
  let nums' := increasingTriplet_zipIdx nums in
  (result = true ->
    increasingTriplet_hasTriplet nums' = true) /\
  (result <> true ->
    increasingTriplet_allNonIncreasing nums' = true).

Theorem increasingTriplet_spec_satisfied
    (nums : list Z)
    (h_precond : increasingTriplet_precond nums) :
  increasingTriplet_postcond
    nums (increasingTriplet nums h_precond) h_precond.
Admitted.
