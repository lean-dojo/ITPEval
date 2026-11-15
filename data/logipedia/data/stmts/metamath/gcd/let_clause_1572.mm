$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1572 (logipedia__metamath__gcd.let_clause_1572), catalog
  title "gcd.let_clause_1572": for natural numbers m and n, the hypotheses
  that n is positive, their greatest common divisor is zero, and both m and n
  are zero imply that m is zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's strict order and gcd are the source
  natural strict order and greatest common divisor, while native equality
  represents logic.eq. The declaration preserves the source quantifier order
  and all four nested hypotheses, including the repeated m = 0 premise and
  conclusion and the jointly inconsistent hypotheses 0 < n and n = 0. The
  final declaration is the artifact's single unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-gcd-let-clause-1572 $a |-
    A. m e. NN0 A. n e. NN0
      (
        0 < n
        ->
        (
          ( m gcd n ) = 0
          ->
          (
            m = 0
            ->
            (
              n = 0
              ->
              m = 0
            )
          )
        )
      )
  $.
$}
