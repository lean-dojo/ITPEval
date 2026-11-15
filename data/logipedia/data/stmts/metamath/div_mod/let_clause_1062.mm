$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.let_clause_1062
  (logipedia__metamath__div_mod.let_clause_1062), catalog title
  "div_mod.let_clause_1062": for natural numbers a, b, q, r, q1, and r1,
  two division-with-remainder specifications, their remainder bounds and
  decomposition equations, and not q at most q1 imply the commuted second
  decomposition of a. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source introduction and elimination declarations make
  div_mod_spec a b q r logically equivalent to

    r < b /\ a = (q x. b) + r.

  Each occurrence of div_mod_spec is expanded by this equivalence. The source
  also repeats each bound and equation as a separate implication hypothesis;
  those hypotheses, the negated order hypothesis, their order, and all six
  universal natural-number quantifiers are retained. The declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d a b q q1 r r1 $.

  logipedia-div-mod-let-clause-1062 $a |-
    A. a e. NN0 A. b e. NN0 A. q e. NN0 A. r e. NN0
      A. q1 e. NN0 A. r1 e. NN0
        (
          ( r < b /\ a = ( ( q x. b ) + r ) )
          ->
          (
            r < b
            ->
            (
              a = ( ( q x. b ) + r )
              ->
              (
                ( r1 < b /\ a = ( ( q1 x. b ) + r1 ) )
                ->
                (
                  r1 < b
                  ->
                  (
                    a = ( ( q1 x. b ) + r1 )
                    ->
                    (
                      -. q <_ q1
                      ->
                      a = ( r1 + ( b x. q1 ) )
                    )
                  )
                )
              )
            )
          )
        )
  $.
$}
