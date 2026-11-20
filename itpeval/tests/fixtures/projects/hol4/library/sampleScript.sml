Theory sample
Ancestors base refuteUnused

Theorem twice_zero:
  twice 0 = 0
Proof
  simp[twice_def]
QED

val _ = save_thm ("under_assumption", ASSUME ``p:bool``);
