$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_mod_spec_intro, catalog title
  "div_mod.div_mod_spec_intro": for natural numbers n, m, q, and r, a
  remainder bound and the division-with-remainder equation imply the
  corresponding division-with-remainder specification. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  LogDivModSpec represents the source module constant div_mod_spec as an
  opaque four-argument proposition. Its first $a declaration supplies only
  wff syntax and asserts no property of that proposition. The restricted
  quantifiers range over all natural numbers in NN0. The two nested
  implications preserve the source hypotheses and their order, and their
  conclusion is the distinct source predicate. The final $a declaration is
  the native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c LogDivModSpec $.

logipedia-div-mod-spec-syntax $a wff ( LogDivModSpec n m q r ) $.

${
  $d m n q r $.

  logipedia-div-mod-div-mod-spec-intro $a |-
    A. n e. NN0 A. m e. NN0 A. q e. NN0 A. r e. NN0
      (
        r < m
        ->
        (
          n = ( ( q x. m ) + r )
          ->
          ( LogDivModSpec n m q r )
        )
      )
  $.
$}
