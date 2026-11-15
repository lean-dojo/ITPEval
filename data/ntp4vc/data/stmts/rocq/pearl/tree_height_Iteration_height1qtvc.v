From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.why3.Ref.Ref.
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Size.
Require Import Why3.bintree.Height.
Open Scope Z_scope.
Inductive cont (α : Type) :=
  | Id : cont α
  | Kleft : tree α -> cont α -> cont α
  | Kright : Z -> cont α -> cont α.
Axiom cont_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (cont α).
Global Existing Instance cont_inhabited.
Arguments Id {α}.
Arguments Kleft {α}.
Arguments Kright {α}.
Inductive what (α : Type) :=
  | Argument : tree α -> what α
  | Result : Z -> what α.
Axiom what_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (what α).
Global Existing Instance what_inhabited.
Arguments Argument {α}.
Arguments Result {α}.
Definition is_id {α : Type} `{Inhabited α} (k : cont α) := match k with | Id => True | _ => False end.
Definition is_result {α : Type} `{Inhabited α} (w : what α) := match w with | Result _ => True | _ => False end.
Axiom evalk : forall {α : Type} `{Inhabited α}, cont α -> Z -> Z.
Axiom evalk_def : forall {α : Type} `{Inhabited α} (k : cont α) (r : Z), evalk k r = (match k with | Id => r | Kleft l k1 => evalk k1 (1%Z + Z.max (height l) r) | Kright x k1 => evalk k1 (1%Z + Z.max x r) end).
Definition evalw {α : Type} `{Inhabited α} (w : what α) : Z := match w with | Argument t => height t | Result x => x end.
Axiom sizek : forall {α : Type} `{Inhabited α}, cont α -> Z.
Axiom sizek_def : forall {α : Type} `{Inhabited α} (k : cont α), sizek k = (match k with | Id => 0%Z | Kleft t k1 => 3%Z + 4%Z * Size.size t + sizek k1 | Kright _ k1 => 1%Z + sizek k1 end).
Definition sizew {α : Type} `{Inhabited α} (w : what α) : Z := match w with | Argument t => 1%Z + 4%Z * Size.size t | Result _ => 0%Z end.
Theorem height1'vc {α : Type} `{Inhabited α} (t : tree α) : evalk (Id : cont α) (evalw (Argument t)) = height t ∧ (∀(k : cont α) (w : what α), evalk k (evalw w) = height t -> (∀(o1 : bool), (if decide (is_id k) then o1 = (if decide (is_result w) then true else false) else o1 = false) -> (if decide (¬ o1 = true) then match k with | Id => (match w with | Argument x => (match x with | Empty => (0%Z ≤ sizek k + sizew w ∧ sizek k + sizew (Result 0%Z) < sizek k + sizew w) ∧ evalk k (evalw (Result 0%Z)) = height t | Node x1 x2 x3 => (0%Z ≤ sizek k + sizew w ∧ sizek (Kleft x3 k) + sizew (Argument x1) < sizek k + sizew w) ∧ evalk (Kleft x3 k) (evalw (Argument x1)) = height t end) | Result x => False end) | Kleft x x1 => (match w with | Argument x2 => (match x2 with | Empty => (0%Z ≤ sizek k + sizew w ∧ sizek k + sizew (Result 0%Z) < sizek k + sizew w) ∧ evalk k (evalw (Result 0%Z)) = height t | Node x3 x4 x5 => (0%Z ≤ sizek k + sizew w ∧ sizek (Kleft x5 k) + sizew (Argument x3) < sizek k + sizew w) ∧ evalk (Kleft x5 k) (evalw (Argument x3)) = height t end) | Result x2 => (0%Z ≤ sizek k + sizew w ∧ sizek (Kright x2 x1) + sizew (Argument x) < sizek k + sizew w) ∧ evalk (Kright x2 x1) (evalw (Argument x)) = height t end) | Kright x x1 => (match w with | Argument x2 => (match x2 with | Empty => (0%Z ≤ sizek k + sizew w ∧ sizek k + sizew (Result 0%Z) < sizek k + sizew w) ∧ evalk k (evalw (Result 0%Z)) = height t | Node x3 x4 x5 => (0%Z ≤ sizek k + sizew w ∧ sizek (Kleft x5 k) + sizew (Argument x3) < sizek k + sizew w) ∧ evalk (Kleft x5 k) (evalw (Argument x3)) = height t end) | Result x2 => (0%Z ≤ sizek k + sizew w ∧ sizek x1 + sizew (Result (1%Z + Z.max x x2)) < sizek k + sizew w) ∧ evalk x1 (evalw (Result (1%Z + Z.max x x2))) = height t end) end else (match w with | Result r => True | _ => False end) ∧ (∀(result : Z), (match w with | Result r => result = r | _ => False end) -> result = height t)))).
Admitted.
