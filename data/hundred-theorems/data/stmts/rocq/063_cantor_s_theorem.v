From Stdlib Require Import Ensembles Classical.

(**
  Cantor's theorem: no function from a type to its powerset is surjective.
  An [Ensemble U] is Rocq's standard-library representation of a subset of
  [U], and equality here is the ordinary equality required by surjectivity.
*)
Section Cantor.

Variable U : Type.

Definition cantor_diagonal (f : U -> Ensemble U) : Ensemble U :=
  fun x => ~ In U (f x) x.

Theorem Cantor_no_surjection (f : U -> Ensemble U) :
  ~ (forall S : Ensemble U, exists x : U, f x = S).
Proof.
  intros surjective.
  destruct (surjective (cantor_diagonal f)) as [x Hx].
  destruct (classic (In U (f x) x)) as [Hin | Hnotin].
  - pose proof Hin as Hdiagonal.
    rewrite Hx in Hdiagonal.
    unfold cantor_diagonal in Hdiagonal.
    exact (Hdiagonal Hin).
  - apply Hnotin.
    rewrite Hx.
    unfold cantor_diagonal.
    exact Hnotin.
Qed.

End Cantor.
