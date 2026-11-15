$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_mod_to_divides
  (logipedia__metamath__gcd.divides_mod_to_divides), catalog title
  "gcd.divides_mod_to_divides": for natural numbers p, m, and positive n,
  if p divides the remainder of m modulo n and p divides n, then p divides
  m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For NN0 values, SetMM integer divisibility is
  equivalent to the source existential natural-multiplier definition of
  primes.divides. The conditional
    if ( n = 0 , m , ( m mod n ) )
  is exactly the source's total div_mod.mod m n; the hypothesis 0 < n selects
  its ordinary natural-remainder branch. The restricted quantifiers and three
  nested implications preserve the source scopes and assumptions exactly.
  The final declaration is the single unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d m n p $.

  logipedia-gcd-divides-mod-to-divides $a |-
    A. p e. NN0 A. m e. NN0 A. n e. NN0
      (
        0 < n
        ->
        (
          p || if ( n = 0 , m , ( m mod n ) )
          ->
          (
            p || n
            ->
            p || m
          )
        )
      )
  $.
$}
