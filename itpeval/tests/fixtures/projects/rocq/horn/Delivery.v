(* An item that is ready and authorized can be delivered and completed. *)
Theorem completion_of_ready (Item : Type) (item : Item)
    (ready permitted delivered complete extra : Item -> Prop)
    (hready : ready item) (hpermitted : permitted item)
    (hdelivered : ready item -> permitted item -> delivered item)
    (hcomplete : delivered item -> complete item) (_hextra : extra item) : complete item.
Proof.
  exact (hcomplete (hdelivered hready hpermitted)).
Qed.
