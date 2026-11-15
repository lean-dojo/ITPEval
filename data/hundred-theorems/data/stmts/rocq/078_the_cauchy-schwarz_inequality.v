(* Cauchy-Schwarz in any dimension *)
(* Compiled with Coq 8.6 *)

Require Import Utf8 List Reals Psatz.
Import ListNotations.

Require Import SummationR.

Notation "u .[ i ]" := (List.nth (pred i) u 0%R)
  (at level 1, format "'[' u '[' .[ i ] ']' ']'").

Theorem fold_Rminus : ∀ x y, (x + - y = x - y)%R.
Proof.
Admitted.

Theorem Rplus_shuffle0 : ∀ n m p : R, (n + m + p)%R = (n + p + m)%R.
Proof.
Admitted.

Definition dot_mul n a b := Σ (k = 1, n), (a.[k] * b.[k]).

Theorem Binet_Cauchy_identity : ∀ (a b c d : list R) n,
  (dot_mul n a c * dot_mul n b d =
   dot_mul n a d * dot_mul n b c +
   Σ (i = 1, n), Σ (j = i + 1, n),
     ((a.[i] * b.[j] - a.[j] * b.[i]) *
      (c.[i] * d.[j] - c.[j] * d.[i])))%R.
Proof.
Admitted.

Theorem Lagrange_identity : ∀ n (a b : list R),
  ((Σ (k = 1, n), (a.[k]²)) * (Σ (k = 1, n), (b.[k]²)) -
     (Σ (k = 1, n), (a.[k] * b.[k]))² =
   Σ (i = 1, n), Σ (j = i + 1, n), ((a.[i] * b.[j] - a.[j] * b.[i])²))%R.
Proof.
Admitted.

Theorem Cauchy_Schwarz_inequality : ∀ (u v : list R) n,
  ((Σ (k = 1, n), (u.[k] * v.[k]))² ≤
   Σ (k = 1, n), (u.[k]²) * Σ (k = 1, n), (v.[k]²))%R.
Proof.
Admitted.

Check Cauchy_Schwarz_inequality.
