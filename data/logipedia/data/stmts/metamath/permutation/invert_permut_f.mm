$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.invert_permut_f
  (logipedia__metamath__permutation.invert_permut_f), catalog title
  "permutation.invert_permut_f": an endofunction of the natural numbers that
  is injective on the initial segment through n has its bounded inverse send
  f(m) back to m whenever m is at most n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. LogInvertPermut n f x is the greatest p at most n
  with f(p) = x, defaulting to zero when there is no such p. This is exactly
  the source recursive invert_permut: its zero case returns zero, and its
  successor case returns the new endpoint when it matches and otherwise
  retains the preceding result.

  The bounded universal formula directly unfolds permutation.injn. Its
  nested implications retain the source order and scope of the two bound
  hypotheses and the equality hypothesis. Native SetMM equality and order
  preserve the corresponding source predicates. The auxiliary $a
  declarations are syntax and a faithful definition; the final $a
  declaration is the unproved corpus statement, and this database contains
  no $p proof declaration.
$)

$c LogInvertPermut $.

log-invert-permut-syntax $a class ( LogInvertPermut n f x ) $.

${
  $d f n p x $.

  log-invert-permut-definition $a |-
    ( LogInvertPermut n f x ) =
      if (
        E. p e. NN0
          ( p <_ n /\ ( f ` p ) = x )
        ,
        sup (
          { p e. NN0 | ( p <_ n /\ ( f ` p ) = x ) }
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
  $d f i j m n $.

  logipedia-permutation-invert-permut-f $a |-
    A. f e. ( NN0 ^m NN0 )
      A. n e. NN0
        A. m e. NN0
          (
            m <_ n
            ->
            (
              A. i e. NN0
                A. j e. NN0
                  (
                    i <_ n
                    ->
                    (
                      j <_ n
                      ->
                      (
                        ( f ` i ) = ( f ` j )
                        ->
                        i = j
                      )
                    )
                  )
              ->
              ( LogInvertPermut n f ( f ` m ) ) = m
            )
          )
  $.
$}
