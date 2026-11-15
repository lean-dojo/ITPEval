$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1545
  (logipedia__metamath__gcd.let_clause_1545), catalog title
  "gcd.let_clause_1545": for natural numbers m and n, a nested chain of
  hypotheses that their gcd is zero, zero divides each number, and each is a
  zero multiple concludes that m is zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's gcd, multiplication, and integer
  divisibility agree with the source natural gcd, multiplication, and
  existential natural-multiplier definition of primes.divides. Native
  equality represents logic.eq. The declaration preserves the original
  quantifier order and every nested implication, including the explicit
  witnesses q1 and q and the redundant divisibility hypotheses. The final
  declaration is the single unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d m n q q1 $.

  logipedia-gcd-let-clause-1545 $a |-
    A. m e. NN0 A. n e. NN0
      (
        ( m gcd n ) = 0
        ->
        (
          0 || n
          ->
          A. q1 e. NN0
            (
              n = ( 0 x. q1 )
              ->
              (
                0 || m
                ->
                A. q e. NN0
                  (
                    m = ( 0 x. q )
                    ->
                    m = 0
                  )
              )
            )
        )
      )
  $.
$}
