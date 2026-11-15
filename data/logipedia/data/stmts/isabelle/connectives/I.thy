(*
  Statement-only formalization of Logipedia corpus artifact connectives.I,
  catalog title "connectives.I": the module's distinguished nullary
  proposition connectives.True holds. This file contains no proof.
*)

theory I
  imports Main
begin

consts logipedia_connectives_True :: bool

theorem connectives_I:
  "logipedia_connectives_True"
  sorry

end
