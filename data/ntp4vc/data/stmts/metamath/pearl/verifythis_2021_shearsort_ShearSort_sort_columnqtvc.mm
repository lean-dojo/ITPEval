$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_columnqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_shearsort_ShearSort_sort_columnqtvc):
  the complete verification condition for copying one integer-matrix column
  into a list, sorting it, and writing it back while preserving every other
  column and the selected column's multiplicities. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCMatrix is the source matrix type represented by its two nonnegative
  integer dimensions and an arbitrary total integer-valued function on
  integer index pairs. This is canonically equivalent to the source's curried
  element function and retains every lookup, including out-of-bounds lookups.
  Integer lists are represented by SetMM words over ZZ. NTP4VCToNat,
  NTP4VCAt, and NTP4VCSet exactly encode Int.toNat, totalized list lookup with
  default zero, and List.set.

  NTP4VCNumof counts an arbitrary total integer function on a finite
  half-open integer interval, and NTP4VCPermut equates those counts for every
  integer. NTP4VCListUpdateLaw retains the generated equality with
  Function.update. NTP4VCMatrixUpdate is the uncurried form of the generated
  nested row-and-column Function.update equality, with equality on the full
  integer-pair domain.

  The remaining biconditional definitions only factor the generated
  verification condition. Expanding them recovers the initial zero list,
  both loop-range branches, every list and matrix state, every integer loop
  index, all length and shape premises, both extensional update premises, the
  abstract sorting postcondition, every prefix and unchanged-column
  invariant, and the final sortedness and permutation conclusions. Source
  let-bound values are replaced only by their defining expressions.

  Every $a before the final declaration is syntax or a faithful definition.
  The final $a is Metamath's native unproved statement encoding, and this
  database contains no $p declaration.
$)

$c
  NTP4VCMatrix NTP4VCRows NTP4VCColumns NTP4VCElts NTP4VCEntry
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCAtMap NTP4VCColumn
  NTP4VCNumof NTP4VCPermut NTP4VCSameShape NTP4VCValidIndex
  NTP4VCPrefix NTP4VCListUpdateLaw NTP4VCMatrixUpdate
  NTP4VCAllZero NTP4VCListSorted NTP4VCOtherColumns
  NTP4VCColumnSorted NTP4VCFinalColumn
  NTP4VCWriteIndexResult NTP4VCWriteIndices NTP4VCWriteExit
  NTP4VCWriteLoopMatrices NTP4VCWriteBack NTP4VCAfterSort
  NTP4VCReadUpdate NTP4VCReadIndices NTP4VCReadExit
  NTP4VCReadLoopArrays NTP4VCNegativeSort NTP4VCCopyAndSort
  NTP4VCMain
$.

sort-column-matrix-syntax
  $a class NTP4VCMatrix $.
sort-column-rows-syntax
  $a class ( NTP4VCRows A ) $.
sort-column-columns-syntax
  $a class ( NTP4VCColumns A ) $.
sort-column-elts-syntax
  $a class ( NTP4VCElts A ) $.
sort-column-entry-syntax
  $a class ( NTP4VCEntry A B C ) $.
sort-column-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
sort-column-at-syntax
  $a class ( NTP4VCAt A B ) $.
sort-column-set-syntax
  $a class ( NTP4VCSet A B C ) $.
sort-column-at-map-syntax
  $a class ( NTP4VCAtMap A ) $.
sort-column-column-syntax
  $a class ( NTP4VCColumn A B ) $.
sort-column-numof-syntax
  $a class ( NTP4VCNumof A B C D ) $.

sort-column-permut-syntax
  $a wff ( NTP4VCPermut A B C D ) $.
sort-column-same-shape-syntax
  $a wff ( NTP4VCSameShape A B ) $.
sort-column-valid-index-syntax
  $a wff ( NTP4VCValidIndex A B C ) $.
sort-column-prefix-syntax
  $a wff ( NTP4VCPrefix A B C D ) $.
sort-column-list-update-law-syntax
  $a wff ( NTP4VCListUpdateLaw A B C ) $.
sort-column-matrix-update-syntax
  $a wff ( NTP4VCMatrixUpdate A B C D E ) $.
sort-column-all-zero-syntax
  $a wff ( NTP4VCAllZero A B ) $.
sort-column-list-sorted-syntax
  $a wff ( NTP4VCListSorted A ) $.
sort-column-other-columns-syntax
  $a wff ( NTP4VCOtherColumns A B C ) $.
sort-column-column-sorted-syntax
  $a wff ( NTP4VCColumnSorted A B ) $.
sort-column-final-column-syntax
  $a wff ( NTP4VCFinalColumn A B C ) $.

sort-column-write-index-result-syntax
  $a wff ( NTP4VCWriteIndexResult A B C D E ) $.
sort-column-write-indices-syntax
  $a wff ( NTP4VCWriteIndices A B C D E ) $.
sort-column-write-exit-syntax
  $a wff ( NTP4VCWriteExit A B C D E ) $.
sort-column-write-loop-matrices-syntax
  $a wff ( NTP4VCWriteLoopMatrices A B C D ) $.
sort-column-write-back-syntax
  $a wff ( NTP4VCWriteBack A B C ) $.
sort-column-after-sort-syntax
  $a wff ( NTP4VCAfterSort A B C ) $.

sort-column-read-update-syntax
  $a wff ( NTP4VCReadUpdate A B C D ) $.
sort-column-read-indices-syntax
  $a wff ( NTP4VCReadIndices A B C D ) $.
sort-column-read-exit-syntax
  $a wff ( NTP4VCReadExit A B C D ) $.
sort-column-read-loop-arrays-syntax
  $a wff ( NTP4VCReadLoopArrays A B C D ) $.
sort-column-negative-sort-syntax
  $a wff ( NTP4VCNegativeSort A B C ) $.
sort-column-copy-and-sort-syntax
  $a wff ( NTP4VCCopyAndSort A B C ) $.
sort-column-main-syntax
  $a wff ( NTP4VCMain A B ) $.

sort-column-matrix-definition $a |- NTP4VCMatrix =
  (
    ( NN0 X. NN0 )
    X.
    ( ZZ ^m ( ZZ X. ZZ ) )
  )
$.

sort-column-rows-definition $a |- (
  NTP4VCRows A
) = (
  1st ` ( 1st ` A )
) $.

sort-column-columns-definition $a |- (
  NTP4VCColumns A
) = (
  2nd ` ( 1st ` A )
) $.

sort-column-elts-definition $a |- (
  NTP4VCElts A
) = (
  2nd ` A
) $.

sort-column-entry-definition $a |- (
  NTP4VCEntry A B C
) = (
  ( NTP4VCElts A ) ` <. B , C >.
) $.

sort-column-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

sort-column-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  sort-column-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d i A $.

  sort-column-at-map-definition $a |- (
    NTP4VCAtMap A
  ) = (
    i e. ZZ |->
      ( NTP4VCAt A i )
  ) $.
$}

${
  $d i A B $.

  sort-column-column-definition $a |- (
    NTP4VCColumn A B
  ) = (
    i e. ZZ |->
      ( NTP4VCEntry A i B )
  ) $.
$}

${
  $d i A B C D $.

  sort-column-numof-definition $a |- (
    NTP4VCNumof A B C D
  ) = (
    # `
    { i e. ( C ..^ D ) |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d v A B C D $.

  sort-column-permut-definition $a |- (
    NTP4VCPermut A B C D
  ) <->
  A. v e. ZZ
    (
      ( NTP4VCNumof A v C D )
      =
      ( NTP4VCNumof B v C D )
    ) $.
$}

sort-column-same-shape-definition $a |- (
  NTP4VCSameShape A B
) <->
(
  ( NTP4VCRows A ) = ( NTP4VCRows B )
  /\
  ( NTP4VCColumns A ) = ( NTP4VCColumns B )
) $.

sort-column-valid-index-definition $a |- (
  NTP4VCValidIndex A B C
) <->
(
  (
    0 <_ B
    /\
    B < ( NTP4VCRows A )
  )
  /\
  (
    0 <_ C
    /\
    C < ( NTP4VCColumns A )
  )
) $.

${
  $d k A B C D $.

  sort-column-prefix-definition $a |- (
    NTP4VCPrefix A B C D
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < D
      )
      ->
      (
        ( NTP4VCAt A k )
        =
        ( NTP4VCEntry B k C )
      )
    ) $.
$}

${
  $d k A B C $.

  sort-column-list-update-law-definition $a |- (
    NTP4VCListUpdateLaw A B C
  ) <->
  (
    k e. ZZ |->
      ( NTP4VCAt ( NTP4VCSet A B C ) k )
  )
  =
  (
    k e. ZZ |->
      if (
        k = B ,
        C ,
        ( NTP4VCAt A k )
      )
  ) $.
$}

${
  $d q A B C D E $.

  sort-column-matrix-update-definition $a |- (
    NTP4VCMatrixUpdate A B C D E
  ) <->
  (
    NTP4VCElts A
  )
  =
  (
    q e. ( ZZ X. ZZ ) |->
      if (
        ( 1st ` q ) = C ,
        if (
          ( 2nd ` q ) = D ,
          E ,
          ( NTP4VCEntry B C ( 2nd ` q ) )
        ) ,
        (
          NTP4VCEntry
            B
            ( 1st ` q )
            ( 2nd ` q )
        )
      )
  ) $.
$}

${
  $d i A B $.

  sort-column-all-zero-definition $a |- (
    NTP4VCAllZero A B
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < B
      )
      ->
      ( NTP4VCAt A i ) = 0
    ) $.
$}

${
  $d i k A $.

  sort-column-list-sorted-definition $a |- (
    NTP4VCListSorted A
  ) <->
  A. i e. ZZ
    A. k e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i <_ k
          )
          /\
          k < ( # ` A )
        )
        ->
        (
          ( NTP4VCAt A i )
          <_
          ( NTP4VCAt A k )
        )
      ) $.
$}

${
  $d i k A B C $.

  sort-column-other-columns-definition $a |- (
    NTP4VCOtherColumns A B C
  ) <->
  A. i e. ZZ
    A. k e. ZZ
      (
        (
          (
            (
              0 <_ i
              /\
              i < ( NTP4VCRows A )
            )
            /\
            (
              0 <_ k
              /\
              k < ( NTP4VCColumns A )
            )
          )
          /\
          -. k = C
        )
        ->
        (
          ( NTP4VCEntry A i k )
          =
          ( NTP4VCEntry B i k )
        )
      ) $.
$}

${
  $d i k A B $.

  sort-column-column-sorted-definition $a |- (
    NTP4VCColumnSorted A B
  ) <->
  A. i e. ZZ
    A. k e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i <_ k
          )
          /\
          k < ( NTP4VCRows A )
        )
        ->
        (
          ( NTP4VCEntry A i B )
          <_
          ( NTP4VCEntry A k B )
        )
      ) $.
$}

sort-column-final-column-definition $a |- (
  NTP4VCFinalColumn A B C
) <->
(
  ( NTP4VCOtherColumns A B C )
  /\
  (
    ( NTP4VCColumnSorted A C )
    /\
    (
      NTP4VCPermut
        ( NTP4VCColumn A C )
        ( NTP4VCColumn B C )
        0
        ( NTP4VCRows A )
    )
  )
) $.

${
  $d n A B C D E $.

  $( A=sorted list, B=original matrix, C=current matrix,
     D=selected column, E=current row. $)
  sort-column-write-index-result-definition $a |- (
    NTP4VCWriteIndexResult A B C D E
  ) <->
  (
    (
      0 <_ E
      /\
      E < ( # ` A )
    )
    /\
    (
      ( NTP4VCValidIndex C E D )
      /\
      A. n e. NTP4VCMatrix
        (
          ( NTP4VCSameShape n C )
          ->
          (
            ( NTP4VCMatrixUpdate n C E D ( NTP4VCAt A E ) )
            ->
            (
              ( NTP4VCPrefix A n D ( E + 1 ) )
              /\
              ( NTP4VCOtherColumns n B D )
            )
          )
        )
    )
  ) $.
$}

${
  $d i A B C D E $.

  $( A=sorted list, B=original matrix, C=current matrix,
     D=selected column, E=last row. $)
  sort-column-write-indices-definition $a |- (
    NTP4VCWriteIndices A B C D E
  ) <->
  A. i e. ZZ
    (
      (
        (
          (
            0 <_ i
            /\
            i <_ E
          )
          /\
          ( NTP4VCPrefix A C D i )
        )
        /\
        ( NTP4VCOtherColumns C B D )
      )
      ->
      ( NTP4VCWriteIndexResult A B C D i )
    ) $.
$}

sort-column-write-exit-definition $a |- (
  NTP4VCWriteExit A B C D E
) <->
(
  (
    ( NTP4VCPrefix A C D ( E + 1 ) )
    /\
    ( NTP4VCOtherColumns C B D )
  )
  ->
  ( NTP4VCFinalColumn C B D )
) $.

${
  $d m A B C D $.

  $( A=sorted list, B=original matrix, C=selected column, D=last row. $)
  sort-column-write-loop-matrices-definition $a |- (
    NTP4VCWriteLoopMatrices A B C D
  ) <->
  A. m e. NTP4VCMatrix
    (
      ( NTP4VCSameShape m B )
      ->
      (
        ( NTP4VCWriteIndices A B m C D )
        /\
        ( NTP4VCWriteExit A B m C D )
      )
    ) $.
$}

sort-column-write-back-definition $a |- (
  NTP4VCWriteBack A B C
) <->
(
  (
    0 <_
    (
      ( ( NTP4VCRows B ) - 1 )
      +
      1
    )
    ->
    (
      ( NTP4VCPrefix A B C 0 )
      /\
      (
        NTP4VCWriteLoopMatrices
          A
          B
          C
          ( ( NTP4VCRows B ) - 1 )
      )
    )
  )
  /\
  (
    (
      (
        ( NTP4VCRows B ) - 1
      )
      +
      1
    )
    <
    0
    ->
    (
      ( NTP4VCColumnSorted B C )
      /\
      (
        NTP4VCPermut
          ( NTP4VCColumn B C )
          ( NTP4VCColumn B C )
          0
          ( NTP4VCRows B )
      )
    )
  )
) $.

${
  $d a A B C $.

  $( A=pre-sort list, B=original matrix, C=selected column. $)
  sort-column-after-sort-definition $a |- (
    NTP4VCAfterSort A B C
  ) <->
  A. a e. Word ZZ
    (
      ( # ` a ) = ( # ` A )
      ->
      (
        (
          ( NTP4VCListSorted a )
          /\
          (
            NTP4VCPermut
              ( NTP4VCAtMap a )
              ( NTP4VCAtMap A )
              0
              ( # ` a )
          )
        )
        ->
        ( NTP4VCWriteBack a B C )
      )
    ) $.
$}

sort-column-read-update-definition $a |- (
  NTP4VCReadUpdate A B C D
) <->
(
  ( NTP4VCValidIndex B D C )
  /\
  (
    (
      0 <_ D
      /\
      D < ( # ` A )
    )
    /\
    (
      (
        #
        `
        (
          NTP4VCSet
            A
            D
            ( NTP4VCEntry B D C )
        )
      )
      =
      ( # ` A )
      ->
      (
        (
          NTP4VCListUpdateLaw
            A
            D
            ( NTP4VCEntry B D C )
        )
        ->
        (
          NTP4VCPrefix
            (
              NTP4VCSet
                A
                D
                ( NTP4VCEntry B D C )
            )
            B
            C
            ( D + 1 )
        )
      )
    )
  )
) $.

${
  $d i A B C D $.

  $( A=current list, B=original matrix, C=selected column, D=last row. $)
  sort-column-read-indices-definition $a |- (
    NTP4VCReadIndices A B C D
  ) <->
  A. i e. ZZ
    (
      (
        (
          (
            0 <_ i
            /\
            i <_ D
          )
          /\
          ( NTP4VCPrefix A B C i )
        )
        ->
        ( NTP4VCReadUpdate A B C i )
      )
    ) $.
$}

sort-column-read-exit-definition $a |- (
  NTP4VCReadExit A B C D
) <->
(
  ( NTP4VCPrefix A B C ( D + 1 ) )
  ->
  ( NTP4VCAfterSort A B C )
) $.

${
  $d a A B C D $.

  $( A=initial list, B=original matrix, C=selected column, D=last row. $)
  sort-column-read-loop-arrays-definition $a |- (
    NTP4VCReadLoopArrays A B C D
  ) <->
  A. a e. Word ZZ
    (
      ( # ` a ) = ( # ` A )
      ->
      (
        ( NTP4VCReadIndices a B C D )
        /\
        ( NTP4VCReadExit a B C D )
      )
    ) $.
$}

${
  $d a A B C $.

  $( A=initial list, B=original matrix, C=selected column. $)
  sort-column-negative-sort-definition $a |- (
    NTP4VCNegativeSort A B C
  ) <->
  A. a e. Word ZZ
    (
      ( # ` a ) = ( # ` A )
      ->
      (
        (
          ( NTP4VCListSorted a )
          /\
          (
            NTP4VCPermut
              ( NTP4VCAtMap a )
              ( NTP4VCAtMap A )
              0
              ( # ` a )
          )
        )
        ->
        ( NTP4VCWriteBack a B C )
      )
    ) $.
$}

sort-column-copy-and-sort-definition $a |- (
  NTP4VCCopyAndSort A B C
) <->
(
  (
    0 <_
    (
      ( ( NTP4VCRows B ) - 1 )
      +
      1
    )
    ->
    (
      ( NTP4VCPrefix A B C 0 )
      /\
      (
        NTP4VCReadLoopArrays
          A
          B
          C
          ( ( NTP4VCRows B ) - 1 )
      )
    )
  )
  /\
  (
    (
      (
        ( NTP4VCRows B ) - 1
      )
      +
      1
    )
    <
    0
    ->
    ( NTP4VCNegativeSort A B C )
  )
) $.

${
  $d a A B $.

  $( A=original matrix, B=selected column. $)
  sort-column-main-definition $a |- (
    NTP4VCMain A B
  ) <->
  (
    0 <_ ( NTP4VCRows A )
    /\
    A. a e. Word ZZ
      (
        (
          ( NTP4VCAllZero a ( NTP4VCRows A ) )
          /\
          ( # ` a ) = ( NTP4VCRows A )
        )
        ->
        ( NTP4VCCopyAndSort a A B )
      )
  ) $.
$}

${
  $d j m $.

  ntp4vc-pearl-verifythis-2021-shearsort-sort-column-vc $a |-
    A. j e. ZZ
      A. m e. NTP4VCMatrix
        (
          (
            0 <_ j
            /\
            j < ( NTP4VCColumns m )
          )
          ->
          ( NTP4VCMain m j )
        )
  $.
$}
