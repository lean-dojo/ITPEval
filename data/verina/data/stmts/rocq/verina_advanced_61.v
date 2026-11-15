(* Statement-only formalization of VERINA corpus artifact verina_advanced_61,
   catalog title "productExceptSelf": executable prefix-and-suffix product
   computation returning at each index the product of all other integers,
   together with its length and indexed-product correctness contract. This
   file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition productExceptSelf_precond (_nums : list Z) : Prop :=
  True.

Definition computepref (nums : list Z) : list Z :=
  fold_left
    (fun acc x => acc ++ [last acc 0 * x])
    nums [1].

Definition computeSuffix (nums : list Z) : list Z :=
  rev
    (fold_left
      (fun acc x => acc ++ [last acc 0 * x])
      (rev nums) [1]).

Definition productExceptSelf
    (nums : list Z)
    (_h_precond : productExceptSelf_precond nums) : list Z :=
  let n := length nums in
  if Nat.eqb n 0%nat
  then []
  else
    let pref := computepref nums in
    let suffix := computeSuffix nums in
    map
      (fun i => nth i pref 0 * nth (S i) suffix 0)
      (seq 0%nat n).

Fixpoint list_myprod (xs : list Z) : Z :=
  match xs with
  | [] => 1
  | x :: rest => x * list_myprod rest
  end.

Definition productExceptSelf_postcond
    (nums result : list Z)
    (_h_precond : productExceptSelf_precond nums) : Prop :=
  length nums = length result /\
  forallb
    (fun i =>
      Z.eqb
        (nth i result 0)
        (list_myprod (firstn i nums) *
         list_myprod (skipn (S i) nums)))
    (seq 0%nat (length nums)) = true.

Theorem productExceptSelf_spec_satisfied
    (nums : list Z)
    (h_precond : productExceptSelf_precond nums) :
  productExceptSelf_postcond
    nums (productExceptSelf nums h_precond) h_precond.
Admitted.
