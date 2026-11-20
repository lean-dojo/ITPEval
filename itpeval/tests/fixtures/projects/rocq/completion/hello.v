Section LocalContext.
Variable P : Prop.
Theorem itpeval_target : P -> P.
Proof.
  exact (fun p => p).
Qed.
End LocalContext.
Check (itpeval_target : forall P : Prop, P -> P).
Print Assumptions itpeval_target.
