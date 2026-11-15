$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1551 (logipedia__metamath__gcd.let_clause_1551), catalog
  title "gcd.let_clause_1551": for natural numbers m and n, if n is zero,
  then every natural number x satisfies n equals x times n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Native equality and multiplication on NN0 represent
  the corresponding source operations. The declaration preserves the unused
  outer parameter m, the quantifier order, the hypothesis 0 = n, and the
  universal conclusion over x (the source variable x347). The final
  declaration is the artifact's single unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d m n x $.

  logipedia-gcd-let-clause-1551 $a |-
    A. m e. NN0 A. n e. NN0
      (
        0 = n
        ->
        A. x e. NN0
          n = ( x x. n )
      )
  $.
$}
