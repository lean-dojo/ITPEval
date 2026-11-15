$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc:
  the generated verification condition for Kadane's two-dimensional
  maximum-sum submatrix algorithm, including array initialization, nested
  row and column loop invariants, and maximality. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source integer matrix is represented by nonnegative integer row and
  column counts together with an arbitrary total function from integer index
  pairs to integers. Each source array is represented by its nonnegative
  integer length and an arbitrary total integer-indexed element function.
  This retains the Why3 Array model directly: lookup is application on the
  full integer domain, so distinct negative indices are not collapsed.

  NTP4VCUpdate is exact full-domain function update on ZZ, and
  NTP4VCUpdateLaw retains the generated extensional update premise.
  NTP4VCArraySum and NTP4VCMatrixSum are the source integer half-open sums.

  The remaining predicates are biconditional factorizations of the generated
  VC. Expanding them recovers every integer, length, and element-function
  quantifier, repeated bound, implication, loop invariant, length premise,
  update-law premise, conditional branch, empty-range branch, and final
  maximality
  conclusion. The source proposition-valued conditional is represented by
  its equivalent guarded cases. The final $a declaration is Metamath's native
  unproved statement encoding; all preceding $a declarations are syntax or
  faithful definitions, and this database contains no $p declaration.
$)

$c
  NTP4VCUpdate NTP4VCUpdateLaw
  NTP4VCArraySum NTP4VCMatrixSum
  NTP4VCZero NTP4VCFill
  NTP4VCCandidate NTP4VCOuterBound NTP4VCInnerBound NTP4VCAllBound
  NTP4VCColumnValues NTP4VCColumnInvariant
  NTP4VCMaximumSubarray NTP4VCAfterMaximum NTP4VCMaximumPhase
  NTP4VCColumnStep NTP4VCColumnRun NTP4VCColumnLoop
  NTP4VCInnerState NTP4VCInnerStates NTP4VCInnerLoop
  NTP4VCFilledArrays NTP4VCOuterIteration NTP4VCFinal
  NTP4VCOuterStates NTP4VCMain
$.

kadane2d-update-syntax
  $a class ( NTP4VCUpdate A B C ) $.
kadane2d-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
kadane2d-array-sum-syntax
  $a class ( NTP4VCArraySum A B C D ) $.
kadane2d-matrix-sum-syntax
  $a class ( NTP4VCMatrixSum A B C D E ) $.

kadane2d-zero-syntax
  $a wff ( NTP4VCZero A B C ) $.
kadane2d-fill-syntax
  $a wff ( NTP4VCFill A B C D E ) $.
kadane2d-candidate-syntax
  $a wff ( NTP4VCCandidate A B C D E F G H ) $.
kadane2d-outer-bound-syntax
  $a wff ( NTP4VCOuterBound A B C D E ) $.
kadane2d-inner-bound-syntax
  $a wff ( NTP4VCInnerBound A B C D E F ) $.
kadane2d-all-bound-syntax
  $a wff ( NTP4VCAllBound A B C D ) $.
kadane2d-column-values-syntax
  $a wff ( NTP4VCColumnValues A B C D E F ) $.
kadane2d-column-invariant-syntax
  $a wff ( NTP4VCColumnInvariant A B C D E F G ) $.
kadane2d-maximum-subarray-syntax
  $a wff ( NTP4VCMaximumSubarray A B C D ) $.
kadane2d-after-maximum-syntax
  $a wff ( NTP4VCAfterMaximum A B C D E F G H I J K L M N ) $.
kadane2d-maximum-phase-syntax
  $a wff ( NTP4VCMaximumPhase A B C D E F G H I J K L ) $.
kadane2d-column-step-syntax
  $a wff ( NTP4VCColumnStep A B C D E F G H ) $.
kadane2d-column-run-syntax
  $a wff ( NTP4VCColumnRun A B C D E F G H I J K L M ) $.
kadane2d-column-loop-syntax
  $a wff ( NTP4VCColumnLoop A B C D E F G H I J K L M ) $.
kadane2d-inner-state-syntax
  $a wff ( NTP4VCInnerState A B C D E F G H I J K L M ) $.
kadane2d-inner-states-syntax
  $a wff ( NTP4VCInnerStates A B C D E F G H ) $.
kadane2d-inner-loop-syntax
  $a wff ( NTP4VCInnerLoop A B C D E F G H I J K ) $.
kadane2d-filled-arrays-syntax
  $a wff ( NTP4VCFilledArrays A B C D E F G H I J K ) $.
kadane2d-outer-iteration-syntax
  $a wff ( NTP4VCOuterIteration A B C D E F G H I J K L ) $.
kadane2d-final-syntax
  $a wff ( NTP4VCFinal A B C D E F G H ) $.
kadane2d-outer-states-syntax
  $a wff ( NTP4VCOuterStates A B C D E F ) $.
kadane2d-main-syntax
  $a wff ( NTP4VCMain A B C D E ) $.

${
  $d k A B C $.

  kadane2d-update-definition $a |- (
    NTP4VCUpdate A B C
  ) = (
    k e. ZZ |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d q A B C D $.

  kadane2d-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C D
  ) <->
  (
    0 <_ A
    /\
    A. q e. ZZ
      (
        ( ( NTP4VCUpdate B C D ) ` q )
        =
        if (
          q = C ,
          D ,
          ( B ` q )
        )
      )
  ) $.
$}

${
  $d k A B C D $.

  kadane2d-array-sum-definition $a |- (
    NTP4VCArraySum A B C D
  ) = sum_ k e.
    ( C ..^ D )
    ( B ` k ) $.
$}

${
  $d i j A B C D E $.

  kadane2d-matrix-sum-definition $a |- (
    NTP4VCMatrixSum A B C D E
  ) = sum_ j e.
    ( D ..^ E )
    (
      sum_ i e.
        ( B ..^ C )
        ( A ` <. i , j >. )
    ) $.
$}

${
  $d i A B C $.

  kadane2d-zero-definition $a |- (
    NTP4VCZero A B C
  ) <->
  (
    0 <_ A
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < C
        )
        ->
        ( B ` i ) = 0
      )
  ) $.
$}

${
  $d i A B C D E $.

  kadane2d-fill-definition $a |- (
    NTP4VCFill A B C D E
  ) <->
  (
    (
      0 <_ A
      /\
      0 <_ C
    )
    /\
    (
      A. i e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < 0
            )
            \/
            (
              ( 0 + E ) <_ i
              /\
              i < C
            )
          )
          ->
          ( D ` i ) = ( B ` i )
        )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( 0 + E )
          )
          ->
          ( D ` i ) = 0
        )
    )
  ) $.
$}

kadane2d-candidate-definition $a |- (
  NTP4VCCandidate A B C D E F G H
) <->
(
  (
    0 <_ D
    /\
    (
      D <_ E
      /\
      E <_ B
    )
  )
  /\
  (
    (
      0 <_ F
      /\
      (
        F <_ G
        /\
        G <_ C
      )
    )
    /\
    (
      H = ( NTP4VCMatrixSum A D E F G )
      /\
      0 <_ ( NTP4VCMatrixSum A D E F G )
    )
  )
) $.

${
  $d p q r s A B C D E $.

  kadane2d-outer-bound-definition $a |- (
    NTP4VCOuterBound A B C D E
  ) <->
  A. p e. ZZ
    A. q e. ZZ
      (
        (
          0 <_ p
          /\
          p < D
        )
        ->
        (
          p <_ q
          /\
          q <_ B
        )
        ->
        A. r e. ZZ
          A. s e. ZZ
            (
              (
                0 <_ r
                /\
                (
                  r <_ s
                  /\
                  s <_ C
                )
              )
              ->
              ( NTP4VCMatrixSum A p q r s ) <_ E
            )
      ) $.
$}

${
  $d p q r s A B C D E F $.

  kadane2d-inner-bound-definition $a |- (
    NTP4VCInnerBound A B C D E F
  ) <->
  A. p e. ZZ
    A. q e. ZZ
      (
        (
          0 <_ p
          /\
          (
            p <_ q
            /\
            q <_ B
          )
        )
        ->
        (
          p < D
          \/
          (
            p = D
            /\
            q < E
          )
        )
        ->
        A. r e. ZZ
          A. s e. ZZ
            (
              (
                0 <_ r
                /\
                (
                  r <_ s
                  /\
                  s <_ C
                )
              )
              ->
              ( NTP4VCMatrixSum A p q r s ) <_ F
            )
      ) $.
$}

${
  $d p q r s A B C D $.

  kadane2d-all-bound-definition $a |- (
    NTP4VCAllBound A B C D
  ) <->
  A. p e. ZZ
    A. q e. ZZ
      (
        (
          0 <_ p
          /\
          (
            p <_ q
            /\
            q <_ B
          )
        )
        ->
        A. r e. ZZ
          A. s e. ZZ
            (
              (
                0 <_ r
                /\
                (
                  r <_ s
                  /\
                  s <_ C
                )
              )
              ->
              ( NTP4VCMatrixSum A p q r s ) <_ D
            )
      ) $.
$}

${
  $d i j A B C D E F $.

  kadane2d-column-values-definition $a |- (
    NTP4VCColumnValues A B C D E F
  ) <->
  (
    0 <_ A
    /\
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < D
        )
        ->
        ( B ` j )
        =
        (
          sum_ i e. ( E ..^ F )
            ( C ` <. i , j >. )
        )
      )
  ) $.
$}

${
  $d i j A B C D E F G $.

  kadane2d-column-invariant-definition $a |- (
    NTP4VCColumnInvariant A B C D E F G
  ) <->
  (
    0 <_ A
    /\
    (
      A. j e. ZZ
        (
          (
            0 <_ j
            /\
            j < G
          )
          ->
          ( B ` j )
          =
          (
            sum_ i e. ( E ..^ F )
              ( C ` <. i , j >. )
          )
        )
      /\
      A. j e. ZZ
        (
          (
            G <_ j
            /\
            j < D
          )
          ->
          ( B ` j )
          =
          (
            sum_ i e. ( E ..^ ( F - 1 ) )
              ( C ` <. i , j >. )
          )
        )
    )
  ) $.
$}

${
  $d l h A B C D $.

  kadane2d-maximum-subarray-definition $a |- (
    NTP4VCMaximumSubarray A B C D
  ) <->
  (
    0 <_ A
    /\
    (
      0 <_ C
      /\
      (
        C <_ D
        /\
        D <_ A
      )
    )
    /\
    A. l e. ZZ
      A. h e. ZZ
        (
          (
            0 <_ l
            /\
            (
              l <_ h
              /\
              h <_ A
            )
          )
          ->
          ( NTP4VCArraySum A B l h )
          <_
          ( NTP4VCArraySum A B C D )
        )
  ) $.
$}

kadane2d-after-maximum-definition $a |- (
  NTP4VCAfterMaximum A B C D E F G H I J K L M N
) <->
(
  (
    L < ( NTP4VCArraySum A B M N )
    ->
    (
      NTP4VCCandidate
        C D E F G M N
        ( NTP4VCArraySum A B M N )
      /\
      (
        NTP4VCInnerBound
          C D E F ( G + 1 )
          ( NTP4VCArraySum A B M N )
        /\
        NTP4VCColumnValues
          A B C E F ( ( G + 1 ) - 1 )
      )
    )
  )
  /\
  (
    -. L < ( NTP4VCArraySum A B M N )
    ->
    (
      NTP4VCCandidate C D E H I J K L
      /\
      (
        NTP4VCInnerBound C D E F ( G + 1 ) L
        /\
        NTP4VCColumnValues
          A B C E F ( ( G + 1 ) - 1 )
      )
    )
  )
) $.

${
  $d l h A B C D E F G H I J K L $.

  kadane2d-maximum-phase-definition $a |- (
    NTP4VCMaximumPhase A B C D E F G H I J K L
  ) <->
  A. l e. ZZ
    A. h e. ZZ
      (
        ( NTP4VCMaximumSubarray A B l h )
        ->
        (
          NTP4VCAfterMaximum
            A B C D E F G H I J K L l h
        )
      ) $.
$}

kadane2d-column-step-definition $a |- (
  NTP4VCColumnStep A B C D E F G H
) <->
(
  (
    (
      0 <_ ( G - 1 )
      /\
      ( G - 1 ) < D
    )
    /\
    (
      0 <_ H
      /\
      H < E
    )
  )
  /\
  (
    (
      0 <_ H
      /\
      H < A
    )
    /\
    (
      (
        0 <_ H
        /\
        H < A
      )
      /\
      (
        A = A
        ->
        (
          (
            NTP4VCUpdateLaw
              A B H
              ( ( B ` H ) + ( C ` <. ( G - 1 ) , H >. ) )
          )
          ->
          (
            NTP4VCColumnInvariant
              A
              (
                NTP4VCUpdate
                  B H
                  ( ( B ` H ) + ( C ` <. ( G - 1 ) , H >. ) )
              )
              C E F G ( H + 1 )
          )
        )
      )
    )
  )
) $.

${
  $d c A B C D E F G H I J K L M $.

  kadane2d-column-run-definition $a |- (
    NTP4VCColumnRun A B C D E F G H I J K L M
  ) <->
  (
    A. c e. ZZ
      (
        (
          (
            0 <_ c
            /\
            c <_ H
          )
          /\
          ( NTP4VCColumnInvariant A B C E F G c )
        )
        ->
        ( NTP4VCColumnStep A B C D E F G c )
      )
    /\
    (
      ( NTP4VCColumnInvariant A B C E F G ( H + 1 ) )
      ->
      (
        NTP4VCMaximumPhase
          A B C D E F G I J K L M
      )
    )
  ) $.
$}

${
  $d n g A B C D E F G H I J K L M $.

  kadane2d-column-loop-definition $a |- (
    NTP4VCColumnLoop A B C D E F G H I J K L M
  ) <->
  (
    (
      0 <_ ( ( E - 1 ) + 1 )
      ->
      (
        ( NTP4VCColumnInvariant A B C E F G 0 )
        /\
        A. n e. ZZ
          A. g e. ( ZZ ^m ZZ )
            (
              (
                0 <_ n
                /\
                n = A
              )
              ->
              (
                NTP4VCColumnRun
                  n g C D E F G ( E - 1 ) I J K L M
              )
            )
      )
    )
    /\
    (
      (
        ( E - 1 ) + 1
      )
      <
      0
      ->
      (
        NTP4VCMaximumPhase
          A B C D E F G I J K L M
      )
    )
  ) $.
$}

${
  $d r A B C D E F G H I J K L M $.

  kadane2d-inner-state-definition $a |- (
    NTP4VCInnerState A B C D E F G H I J K L M
  ) <->
  A. r e. ZZ
    (
      (
        (
          G <_ r
          /\
          r <_ H
        )
        /\
        (
          NTP4VCCandidate C D E I J K L M
          /\
          (
            NTP4VCInnerBound C D E F r M
            /\
            NTP4VCColumnValues A B C E F ( r - 1 )
          )
        )
      )
      ->
      (
        NTP4VCColumnLoop
          A B C D E F r H I J K L M
      )
    ) $.
$}

${
  $d p q r s t n g A B C D E F G H $.

  kadane2d-inner-states-definition $a |- (
    NTP4VCInnerStates A B C D E F G H
  ) <->
  A. p e. ZZ
    A. q e. ZZ
      A. r e. ZZ
        A. s e. ZZ
          A. t e. ZZ
            A. n e. ZZ
              A. g e. ( ZZ ^m ZZ )
                (
                  (
                    0 <_ n
                    /\
                    n = A
                  )
                  ->
                  (
                    (
                      NTP4VCInnerState
                        n g C D E F G H s r q p t
                    )
                    /\
                    (
                      (
                        NTP4VCCandidate C D E s r q p t
                        /\
                        (
                          NTP4VCInnerBound C D E F ( H + 1 ) t
                          /\
                          NTP4VCColumnValues
                            n N C E F ( ( H + 1 ) - 1 )
                        )
                      )
                      ->
                      (
                        NTP4VCCandidate C D E s r q p t
                        /\
                        NTP4VCOuterBound C D E ( F + 1 ) t
                      )
                    )
                  )
                ) $.
$}

kadane2d-inner-loop-definition $a |- (
  NTP4VCInnerLoop A B C D E F G H I J K
) <->
(
  (
    ( F + 1 ) <_ ( D + 1 )
    ->
    (
      (
        NTP4VCCandidate C D E G H I J K
        /\
        (
          NTP4VCInnerBound C D E F ( F + 1 ) K
          /\
          NTP4VCColumnValues
            A B C E F ( ( F + 1 ) - 1 )
        )
      )
      /\
      (
        NTP4VCInnerStates
          A B C D E F ( F + 1 ) D
      )
    )
  )
  /\
  (
    ( D + 1 ) < ( F + 1 )
    ->
    (
      NTP4VCCandidate C D E G H I J K
      /\
      NTP4VCOuterBound C D E ( F + 1 ) K
    )
  )
) $.

${
  $d n g A B C D E F G H I J K $.

  kadane2d-filled-arrays-definition $a |- (
    NTP4VCFilledArrays A B C D E F G H I J K
  ) <->
  A. n e. ZZ
    A. g e. ( ZZ ^m ZZ )
      (
        (
          0 <_ n
          /\
          n = A
        )
        ->
        (
          ( NTP4VCFill A B n g E )
          ->
          (
            NTP4VCInnerLoop
              n g C D E F G H I J K
          )
        )
      ) $.
$}

kadane2d-outer-iteration-definition $a |- (
  NTP4VCOuterIteration A B C D E F G H I J K L
) <->
(
  (
    (
      0 <_ F
      /\
      F <_ G
    )
    /\
    (
      NTP4VCCandidate C D E H I J K L
      /\
      NTP4VCOuterBound C D E F L
    )
  )
  ->
  (
    (
      0 <_ 0
      /\
      (
        0 <_ E
        /\
        ( 0 + E ) <_ A
      )
    )
    /\
    (
      NTP4VCFilledArrays
        A B C D E F H I J K L
    )
  )
) $.

kadane2d-final-definition $a |- (
  NTP4VCFinal A B C D E F G H
) <->
(
  (
    0 <_ D
    /\
    (
      D <_ E
      /\
      E <_ B
    )
  )
  /\
  (
    (
      0 <_ F
      /\
      (
        F <_ G
        /\
        G <_ C
      )
    )
    /\
    (
      H = ( NTP4VCMatrixSum A D E F G )
      /\
      ( NTP4VCAllBound A B C H )
    )
  )
) $.

${
  $d p q r s t n g u A B C D E F $.

  kadane2d-outer-states-definition $a |- (
    NTP4VCOuterStates A B C D E F
  ) <->
  A. p e. ZZ
    A. q e. ZZ
      A. r e. ZZ
        A. s e. ZZ
          A. t e. ZZ
            A. n e. ZZ
              A. g e. ( ZZ ^m ZZ )
                (
                  (
                    0 <_ n
                    /\
                    n = A
                  )
                  ->
                  (
                    A. u e. ZZ
                      (
                        NTP4VCOuterIteration
                          n g C D E u F s r q p t
                      )
                    /\
                    (
                      (
                        NTP4VCCandidate C D E s r q p t
                        /\
                        NTP4VCOuterBound C D E ( F + 1 ) t
                      )
                      ->
                      (
                        NTP4VCFinal C D E s r q p t
                      )
                    )
                  )
                ) $.
$}

kadane2d-main-definition $a |- (
  NTP4VCMain A B C D E
) <->
(
  (
    0 <_ ( ( D - 1 ) + 1 )
    ->
    (
      (
        NTP4VCCandidate C D E 0 0 0 0 0
        /\
        NTP4VCOuterBound C D E 0 0
      )
      /\
      (
        NTP4VCOuterStates A B C D E ( D - 1 )
      )
    )
  )
  /\
  (
    ( ( D - 1 ) + 1 ) < 0
    ->
    (
      NTP4VCFinal C D E 0 0 0 0 0
    )
  )
) $.

${
  $d m n f k g $.

  ntp4vc-pearl-verifythis-2017-maximum-sum-submatrix-kadane2d-vc $a |-
    A. m e. ZZ
      A. n e. ZZ
        A. f e. ( ZZ ^m ( ZZ X. ZZ ) )
          (
            (
              0 <_ m
              /\
              0 <_ n
            )
            ->
            (
              0 <_ n
              /\
              A. k e. ZZ
                A. g e. ( ZZ ^m ZZ )
                  (
                    (
                      (
                        0 <_ k
                        /\
                        ( NTP4VCZero k g n )
                      )
                      /\
                      k = n
                    )
                    ->
                    ( NTP4VCMain k g f m n )
                  )
            )
          )
  $.
$}
