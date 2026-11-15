$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/word_common_factor_Top_powerqtvc: the recursive word-power
  verification condition states that the predecessor of a nonzero
  nonnegative integer is smaller and remains nonnegative. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. The source let-bound value
  o1 is inlined definitionally as A - 1. The integer parameter and the two
  source assumptions are retained as scoped essential hypotheses, which is
  equivalent to the source curried theorem. The repeated nonnegativity fact,
  strict predecessor bound, conjunction nesting, and predecessor
  nonnegativity conclusion are preserved exactly. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $( Source theorem parameter A=n; the let-bound o1 is expanded as A - 1. $)

  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-fact0 $e |- 0 <_ A $.
  ntp4vc-fact1 $e |- A =/= 0 $.

  ntp4vc-pearl-word-common-factor-top-power-vc $a |- (
    (
      0 <_ A
      /\
      ( A - 1 ) < A
    )
    /\
    0 <_ ( A - 1 )
  ) $.
$}
