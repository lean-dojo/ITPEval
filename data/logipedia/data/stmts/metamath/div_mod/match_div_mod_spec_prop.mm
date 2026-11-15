$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.match_div_mod_spec_prop, catalog title
  "div_mod.match_div_mod_spec_prop": elimination of the natural-number
  quotient-remainder specification into an arbitrary proposition from its
  remainder bound and decomposition equation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivModSpec represents the source module constant div_mod_spec as an
  opaque four-argument proposition. Its first $a declaration supplies only
  wff syntax and asserts no property of that proposition. Metamath's wff
  metavariable ph ranges schematically over the source return : Prop. The
  restricted quantifiers range over all natural numbers in NN0, and the
  nested implications preserve the source continuation and eliminator
  exactly. The final $a declaration is the native unproved statement
  encoding; this artifact's root statement file contains no $p proof
  declaration.
$)

$c LogDivModSpec $.

logipedia-div-mod-spec-syntax $a wff ( LogDivModSpec n m q r ) $.

${
  $d m n q r $.

  logipedia-div-mod-match-div-mod-spec-prop $a |-
    A. n e. NN0 A. m e. NN0 A. q e. NN0 A. r e. NN0
      (
        (
          r < m
          ->
          ( n = ( ( q x. m ) + r ) -> ph )
        )
        ->
        (
          ( LogDivModSpec n m q r )
          ->
          ph
        )
      )
  $.
$}
