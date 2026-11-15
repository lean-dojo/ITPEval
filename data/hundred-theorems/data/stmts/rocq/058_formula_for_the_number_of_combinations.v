Require Import FSets MapFunction.
Require Import Arith EqNat Euclid ArithRing ZArith.
Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

(* Cardinality functions used by the powerset statements below. *)
Fixpoint two_power (n:nat) : nat := match n with
 | O => 1
 | S n => 2 * (two_power n)
 end.

Fixpoint binomial n k { struct n } := match n, k with
  | _, O => 1
  | O, _ => 0
  | S n', S k' => binomial n' k' + binomial n' k
 end.

Fixpoint fact n := match n with
  | O => 1
  | S n' => n * (fact n')
 end.

Lemma binomial_0 : forall n k, k>n -> binomial n k = 0.
Proof.
Admitted.

Lemma binomial_rec : forall n k, k<=n -> 
 (binomial n k)*(fact k * fact (n-k)) = fact n.
Proof.
Admitted.

Lemma fact_pos : forall k, fact k > 0.
Proof.
Admitted.

Lemma binomial_den_pos : forall n k, fact k * fact (n-k) > 0.
Proof.
Admitted.

Definition binomial' n k := 
 let (q,_) := quotient (fact k * fact (n-k)) (binomial_den_pos n k) (fact n)
 in q.

Lemma binomial_alt : forall n k, k<=n -> 
 binomial n k = binomial' n k.
Proof.
Admitted.


Module PowerSet (M:S).

(* M is our base sets structure. *)
(* MM is a "sets of sets" structure: *)
Module MM := FSetList.Make M.
(* Adding a map function to MM... *)
Module MM' := MapFunction.MapFunction MM.
(* Properties functors *)
Module P := FSetProperties.Properties M.
Module P' := FSetProperties.OrdProperties M.
Module F := P.FM.
Module PEP := FSetEqProperties.EqProperties MM.
Module PP := PEP.MP.
Module FF := PP.FM.
Module ME := OrderedTypeFacts M.E.

Infix "[=]" := M.Equal (at level 70, no associativity).
Infix "[==]" := MM.Equal (at level 70, no associativity).

(** Computing the set of all subsets of a particular set [s] *)

Definition powerset s := 
  M.fold 
   (fun (x:M.elt)(ss:MM.t) => MM.union ss (MM'.map (M.add x) ss)) 
   s 
   (MM.singleton M.empty).

(** Proofs about powerset *)

Lemma map_add : forall s s' x, MM.In s' (MM'.map (M.add x) s)
 <-> M.In x s' /\ (MM.In s' s \/ MM.In (M.remove x s') s).
Proof.
Admitted.

Lemma compat_op_pow :
 compat_op M.E.eq MM.Equal
  (fun x0 ss => MM.union ss (MM'.map (M.add x0) ss)).
Proof.
Admitted.
Hint Resolve compat_op_pow : set.

Lemma singleton_empty : forall s, MM.In s (MM.singleton M.empty) <-> M.Empty s.
Proof.
Admitted.

Lemma powerset_base : forall s, M.Empty s -> powerset s [==] MM.singleton M.empty.
Proof.
Admitted.

Lemma powerset_step : forall s1 s2 x, P'.Above x s1 -> P.Add x s1 s2 ->
 powerset s2 [==] MM.union (powerset s1) (MM'.map (M.add x) (powerset s1)).
Proof.
Admitted.

Lemma powerset_is_powerset:
 forall s s', MM.In s' (powerset s) <-> M.Subset s' s.
Proof.
Admitted.

Lemma powerset_cardinal:
 forall s, MM.cardinal (powerset s) = two_power (M.cardinal s).
Proof.
Admitted.

(** Computing the set of all subsets of cardinal k for a particular set [s] *)

Definition powerset_k s k := 
 MM.filter (fun s => beq_nat (M.cardinal s) k) (powerset s).


(** Proofs about powerset_k *)

Lemma powerset_k_is_powerset_k : forall k s s', 
 MM.In s' (powerset_k s k) <-> M.Subset s' s /\ M.cardinal s' = k.
Proof.
Admitted.

Lemma powerset_k_cardinal : forall s k, 
 MM.cardinal (powerset_k s k) = binomial (M.cardinal s) k.
Proof.
Admitted.

(** A more "direct" definition *)

Definition powerset_k' s := 
  M.fold 
  (fun (x:M.elt)(ff:nat->MM.t)(k:nat) => match k with 
    | O => ff 0
    | S k' => MM.union (ff k) (MM'.map (M.add x) (ff k'))
   end) 
  s 
  (fun k => if k then MM.singleton M.empty else MM.empty).

Lemma powerset_k'_is_powerset_k:
 forall s s' k, MM.In s' (powerset_k' s k) <->
  M.Subset s' s /\ M.cardinal s' = k.
Proof.
Admitted.

Lemma powerset_k_alt : 
 forall s k, powerset_k' s k [==] powerset_k s k.
Proof.
Admitted.

End PowerSet.

(** An example: *)

Open Scope positive_scope.

Module P := FSetList.Make Positive_as_OT.
Module PS := PowerSet P.
Module PP := PS.MM.

(* The set containing numbers 1..n *)
Fixpoint interval (n:nat) {struct n} : P.t := match n with 
 | O => P.empty
 | S n => P.add (P_of_succ_nat n) (interval n)
 end.

Eval vm_compute in P.elements (interval 10).

Definition powerset_5 := PS.powerset (interval 5).

Eval vm_compute in map P.elements (PP.elements powerset_5).

Definition subsets_size2_in5 := PS.powerset_k' (interval 5) 2. 

Eval vm_compute in map P.elements (PP.elements subsets_size2_in5).




