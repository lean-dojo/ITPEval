$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_mod_spec_to_eq2, catalog title
  "div_mod.div_mod_spec_to_eq2": for natural numbers a, b, q, r, q1, and r1,
  any two division-with-remainder specifications for the same a and b have
  equal remainders r and r1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source introduction and elimination declarations make
  div_mod_spec a b q r logically equivalent to

    r < b /\ a = (q x. b) + r.

  Both source predicate hypotheses are expanded by this equivalence. Their
  order, the six universal natural-number quantifiers, and the remainder
  equality conclusion are unchanged. The declaration is an unproved $a
  statement encoding; this artifact's root statement file contains no $p
  proof declaration.
$)

${
  $d a b q q1 r r1 $.

  logipedia-div-mod-div-mod-spec-to-eq2 $a |-
    A. a e. NN0 A. b e. NN0 A. q e. NN0 A. r e. NN0
      A. q1 e. NN0 A. r1 e. NN0
        (
          ( r < b /\ a = ( ( q x. b ) + r ) )
          ->
          (
            ( r1 < b /\ a = ( ( q1 x. b ) + r1 ) )
            ->
            r = r1
          )
        )
  $.
$}
