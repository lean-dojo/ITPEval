$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.injective_invert_permut
  (logipedia__metamath__permutation.injective_invert_permut), catalog title
  "permutation.injective_invert_permut": the bounded inverse of a
  natural-number permutation of the initial segment through n is injective
  on that segment. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. LogInvertPermut n f m is the greatest p at most n
  with f(p) = m, defaulting to zero when there is no such p. This is exactly
  the source recursive invert_permut: its zero case returns zero, and its
  successor case returns the new endpoint when it matches and otherwise
  retains the preceding result.

  The antecedent directly unfolds permutation.permut: f maps the initial
  segment through n into itself and is injective there. The conclusion
  directly unfolds permutation.injn for LogInvertPermut n f. Grouping the
  curried source implications into conjunctive antecedents is a
  bidirectional propositional equivalence. The auxiliary $a declarations
  are syntax and a faithful definition; the final $a declaration is the
  unproved corpus statement, and this database contains no $p proof
  declaration.
$)

$c LogInvertPermut $.

log-invert-permut-syntax $a class ( LogInvertPermut n f m ) $.

${
  $d f m n p $.

  log-invert-permut-definition $a |-
    ( LogInvertPermut n f m ) =
      if (
        E. p e. NN0
          ( p <_ n /\ ( f ` p ) = m )
        ,
        sup (
          { p e. NN0 | ( p <_ n /\ ( f ` p ) = m ) }
          ,
          NN0
          ,
          <
        )
        ,
        0
      )
  $.
$}

${
  $d f i j n $.

  logipedia-permutation-injective-invert-permut $a |-
    A. f e. ( NN0 ^m NN0 )
      A. n e. NN0
        (
          (
            A. i e. NN0
              (
                i <_ n
                ->
                ( f ` i ) <_ n
              )
            /\
            A. i e. NN0
              A. j e. NN0
                (
                  (
                    ( i <_ n /\ j <_ n )
                    /\
                    ( f ` i ) = ( f ` j )
                  )
                  ->
                  i = j
                )
          )
          ->
          A. i e. NN0
            A. j e. NN0
              (
                (
                  ( i <_ n /\ j <_ n )
                  /\
                  ( LogInvertPermut n f i ) =
                    ( LogInvertPermut n f j )
                )
                ->
                i = j
              )
        )
  $.
$}
