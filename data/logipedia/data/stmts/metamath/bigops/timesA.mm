$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.timesA, catalog title "bigops.timesA": the source module's opaque
  polymorphic Aop predicate holds for one in the natural-number domain.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogAop h x is the source primitive proposition Aop h x. The carrier
  argument NN0 represents nat, and 1 represents S O. The syntax declaration
  and the artifact assertion are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c LogAop $.

log-aop-syntax $a wff ( LogAop h x ) $.

logipedia-bigops-timesa $a |- ( LogAop NN0 1 ) $.
