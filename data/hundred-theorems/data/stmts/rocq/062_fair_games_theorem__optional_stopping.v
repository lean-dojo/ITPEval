(*
  The discrete-time optional stopping theorem.  The stopped value and all
  three standard sufficient conditions are explicit in the statement.
*)

Require Import QArith Morphisms Equivalence Program.Basics Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.
Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Export ConditionalExpectation.
Require Import RbarExpectation Event Almost DVector utils.Utils List PushNeg.
Require Import Reals Coquelicot.Rbar Coquelicot.Lim_seq Martingale.

Set Bullet Behavior "Strict Subproofs".

Section StoppedProcessDefinitions.

Context {Ts : Type}.

Definition lift1_min (n : nat) (time : option nat) : nat :=
  match time with
  | None => n
  | Some k => min n k
  end.

Definition process_stopped_at
    (Y : nat -> Ts -> R) (T : Ts -> option nat)
    (n : nat) (omega : Ts) : R :=
  Y (lift1_min n (T omega)) omega.

Definition process_under
    (Y : nat -> Ts -> R) (T : Ts -> option nat)
    (omega : Ts) : R :=
  match T omega with
  | None => 0
  | Some n => Y n omega
  end.

End StoppedProcessDefinitions.

Local Existing Instance Rge_pre.
Local Existing Instance Rle_pre.

Section OptionalStopping.

Context
  {Ts : Type}
  {sigma : SigmaAlgebra Ts}
  (prts : ProbSpace sigma)
  (F : nat -> SigmaAlgebra Ts)
  {filt : IsFiltration F}
  {sub : IsSubAlgebras sigma F}
  (tau : Ts -> option nat)
  {is_stop : IsStoppingTime tau F}
  (Y : nat -> Ts -> R)
  {rv : forall n, RandomVariable sigma borel_sa (Y n)}
  {isfe : forall n, IsFiniteExpectation prts (Y n)}
  {adapt : IsAdapted borel_sa Y F}
  (conditions :
    (exists N : nat,
       almost prts
         (fun omega =>
            match tau omega with
            | Some k => (k <= N)%nat
            | None => False
            end))
    \/
    (almost prts (fun omega => tau omega <> None) /\
     exists K : R,
       forall n, almost prts (fun omega => Rabs (Y n omega) < K))
    \/
    (Rbar_IsFiniteExpectation prts
       (fun omega =>
          match tau omega with
          | Some n => INR n
          | None => p_infty
          end) /\
     exists K : R,
       forall n,
         almost prts
           (fun omega => Rabs (Y (S n) omega - Y n omega) <= K))).

Instance optional_stopping_time_isfe :
  IsFiniteExpectation prts (process_under Y tau).
Proof.
Admitted.

Theorem optional_stopping_time
    {mart : IsMartingale prts eq Y F} :
  FiniteExpectation prts (process_under Y tau) =
  FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.

Theorem optional_stopping_time_sub
    {mart : IsMartingale prts Rle Y F} :
  FiniteExpectation prts (process_under Y tau) >=
  FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.

Theorem optional_stopping_time_super
    {mart : IsMartingale prts Rge Y F} :
  FiniteExpectation prts (process_under Y tau) <=
  FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.

End OptionalStopping.
