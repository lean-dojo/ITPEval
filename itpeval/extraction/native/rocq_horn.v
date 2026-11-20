From Ltac2 Require Import Ltac2.

(* Read local hypotheses from the elaborated proof state without solving goals. *)

Ltac2 with_separator separator left right :=
  Message.concat left (Message.concat (Message.of_string separator) right).

Ltac2 print_field field value :=
  let label := with_separator " " (Message.of_string "ITPEVAL_ROCQ_HORN")
    (Message.of_string field) in
  Message.print (with_separator " " label value).

Ltac2 local_name term :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var name => Some (Message.of_ident name)
  | _ => None
  end.

Ltac2 proposition term := Constr.equal (Constr.type term) constr:(Prop).

Ltac2 atom_name term :=
  if Constr.has_evar term then None else
  if proposition term then
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.App head args =>
      Array.fold_left (fun prefix arg =>
        match prefix, local_name arg with
        | Some left, Some right => Some (with_separator " " left right)
        | _, _ => None
        end) (local_name head) args
    | _ => local_name term
    end
  else None.

Ltac2 rec horn_type term antecedents :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Prod binder body =>
    if Constr.Unsafe.is_closed body then
      match atom_name (Constr.Binder.type binder) with
      | Some antecedent => horn_type body (antecedent :: antecedents)
      | None => None
      end
    else None
  | _ =>
    match atom_name term with
    | Some consequent => Some (consequent, List.rev antecedents)
    | None => None
    end
  end.

Ltac2 print_hypothesis binding :=
  let (name, _, type) := binding in
  if proposition type then
    let printed_name := Message.of_ident name in
    match horn_type type [] with
    | Some (consequent, antecedents) =>
      let fields := List.fold_left (with_separator "|")
        (with_separator "|" printed_name consequent) antecedents in
      print_field "hypothesis" fields
    | None => print_field "skipped" printed_name
    end
  else ().

Ltac2 observe () :=
  let goal := Control.goal () in
  print_field "goal" (Message.of_lconstr goal);
  match atom_name goal with
  | Some conclusion => print_field "conclusion" conclusion
  | None => ()
  end;
  List.iter print_hypothesis (Control.hyps ());
  print_field "end" (Message.of_string "state").
