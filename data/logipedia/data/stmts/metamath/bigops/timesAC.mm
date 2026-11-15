$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.timesAC, catalog title "bigops.timesAC": the source module's opaque
  polymorphic ACop predicate holds for one in the natural-number domain.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogACop A B is the source primitive proposition ACop A B, with both
  operands represented by SetMM class expressions. The class NN0 represents
  nat, and the class 1 represents S O. The local syntax declaration and
  artifact assertion are unproved $a statement encodings; this artifact
  contributes no $p proof declaration.
$)

$c LogACop $.

log-acop-syntax $a wff ( LogACop A B ) $.

logipedia-bigops-timesac $a |- ( LogACop NN0 1 ) $.
