$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.let_clause_1063
  (logipedia__metamath__permutation.let_clause_1063), catalog title
  "permutation.let_clause_1063": for a bounded natural-number permutation,
  equality of two bounded inputs transfers the stated value j from the
  second input to the first, under the source's full chain of bounds,
  value equations, range, and injectivity assumptions. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. The first antecedent unfolds permutation.permut as
  preservation of the initial segment through n together with injectivity
  there. Each later occurrence of permutation.injn is likewise unfolded as
  equality reflection for arbitrary natural indices at most n. Restricted
  quantifiers, conjunctions, and nested implications preserve every source
  binder and assumption, including the repeated range and injectivity
  hypotheses. Native SetMM equality and order represent the corresponding
  source predicates. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d a b f i j k n p q $.

  logipedia-permutation-let-clause-1063 $a |-
    A. f e. ( NN0 ^m NN0 )
      A. n e. NN0
        (
          (
            (
              A. k e. NN0
                (
                  k <_ n
                  ->
                  ( f ` k ) <_ n
                )
            )
            /\
            A. p e. NN0
              A. q e. NN0
                (
                  p <_ n
                  ->
                  (
                    q <_ n
                    ->
                    (
                      ( f ` p ) = ( f ` q )
                      ->
                      p = q
                    )
                  )
                )
          )
          ->
          A. i e. NN0
            A. j e. NN0
              (
                i <_ n
                ->
                (
                  j <_ n
                  ->
                  A. a e. NN0
                    (
                      (
                        a <_ n
                        /\
                        ( f ` a ) = i
                      )
                      ->
                      (
                        a <_ n
                        ->
                        (
                          ( f ` a ) = i
                          ->
                          A. b e. NN0
                            (
                              (
                                b <_ n
                                /\
                                ( f ` b ) = j
                              )
                              ->
                              (
                                b <_ n
                                ->
                                (
                                  ( f ` b ) = j
                                  ->
                                  (
                                    A. k e. NN0
                                      (
                                        k <_ n
                                        ->
                                        ( f ` k ) <_ n
                                      )
                                    ->
                                    (
                                      (
                                        A. p e. NN0
                                          A. q e. NN0
                                            (
                                              p <_ n
                                              ->
                                              (
                                                q <_ n
                                                ->
                                                (
                                                  ( f ` p ) = ( f ` q )
                                                  ->
                                                  p = q
                                                )
                                              )
                                            )
                                      )
                                      ->
                                      (
                                        a = b
                                        ->
                                        ( f ` a ) = j
                                      )
                                    )
                                  )
                                )
                              )
                            )
                        )
                      )
                    )
                )
              )
        )
  $.
$}
