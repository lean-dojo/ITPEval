(*
MIT License

Copyright (c) 2017 Jean-Marie Madiot, INRIA

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

Require Import Arith.
Require Import List.
Require Import Permutation.
Import ListNotations.

Definition normalize_direction : nat * nat -> nat * nat :=
  fun p => if fst p <=? snd p then p else (snd p, fst p).

Definition eulerian (E path : list (nat * nat)) :=
  Permutation
    (map normalize_direction E)
    (map normalize_direction path).

Inductive path : list (nat * nat) -> Prop :=
  | path_nil : path []
  | path_singleton x y : path [(x, y)]
  | path_cons x y z l :
      path ((y, z) :: l) ->
      path ((x, y) :: (y, z) :: l).

Fixpoint pathb l :=
  (match l with
  | [] => true
  | [(_, _)] => true
  | (x, y) :: (((y', z) :: _) as l) =>
    (y =? y') && pathb l
  end)%bool.

Lemma pathb_correct l : pathb l = true <-> path l.
Proof.
Admitted.

Fixpoint pathbdir (swapfirst : bool) l :=
  (match l with
  | [] => true
  | [(_, _)] => true
  | (x, y) :: (((z, t) :: _) as l) =>
    let xy := if swapfirst then x else y in
    ((xy =? z) && pathbdir false l) ||
    ((xy =? t) && pathbdir true l)
  end)%bool.

Lemma pathbdir_rewrite first x y z t l :
  pathbdir first ((x, y) :: (z, t) :: l) =
  ((((if first then x else y) =? z) && pathbdir false ((z, t) :: l))
   || ((if first then x else y) =? t) && pathbdir true ((z, t) :: l))%bool.
Proof.
Admitted.

Definition shouldswap p :=
  match p with
  | [] => true
  | (x, y) :: _ => negb (x <=? y)
  end.

Lemma pathbdir_correct p :
  pathb p = true ->
  pathbdir (shouldswap p) (map normalize_direction p) = true.
Proof.
Admitted.

Fixpoint remove1 {A} (eq_dec : forall x y, {x = y} + {x <> y}) (x : A) l : list A :=
  match l with
  | [] => []
  | y :: tl => if eq_dec x y then tl else y :: remove1 eq_dec x tl
  end.

Lemma permutation_remove1 {A} eq_dec (a : A) l l' :
  Permutation l l' ->
  Permutation (remove1 eq_dec a l) (remove1 eq_dec a l').
Proof.
Admitted.

Lemma pe : forall x y : nat * nat, {x = y} + {x <> y}.
Proof.
Admitted.

Fixpoint find x l :=
  match l with
    [] => False
  | y :: l => if pe x y then True else find x l
  end.

Lemma prune x l l' : Permutation (x :: l) l' -> find x l'.
Proof.
Admitted.

Lemma permutation_remove {A} eq_dec (a : A) l l' :
  Permutation (a :: l) l' ->
  Permutation l (remove1 eq_dec a l').
Proof.
Admitted.

Theorem konigsberg_bridges :
  let E := [(0, 1); (0, 2); (0, 3); (1, 2); (1, 2); (2, 3); (2, 3)] in
  forall p, path p -> eulerian E p -> False.
Proof.
Admitted.
