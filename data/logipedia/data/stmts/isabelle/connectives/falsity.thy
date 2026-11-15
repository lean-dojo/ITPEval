(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.falsity, catalog title "connectives.falsity": the principle of
  explosion from the module's primitive falsity proposition to every
  proposition. This file contains no proof.
*)

theory falsity
  imports Main
begin

consts logipedia_connectives_False :: bool

theorem connectives_falsity:
  "\<forall>t :: bool. logipedia_connectives_False \<longrightarrow> t"
  sorry

end
