$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc):
  the complete verification condition for sorting every column of an integer
  matrix, either directly or by transposing, sorting rows, and transposing
  back. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCMatrix is exactly the source matrix type: a pair of nonnegative
  integer dimensions together with an arbitrary total function from integer
  index pairs to integers. NTP4VCEntry therefore retains all source lookups,
  including lookups outside the valid rectangular index range.

  NTP4VCNumof counts occurrences on an arbitrary finite half-open integer
  interval, and NTP4VCPermut equates those counts for every integer. The
  remaining biconditional definitions factor the generated verification
  condition. Expanding them recovers the existential Boolean choice, the
  universally quantified guarded branch, both loop initializations, every
  intermediate matrix and loop-index quantifier, the column- and row-sort
  contracts, both transpose contracts, all permutation invariants, all
  sorted-prefix invariants, and the final column permutation and sortedness
  conclusions. Boolean values use SetMM's two-element set { 0, 1 }, with 1
  true and 0 false. Let-bound values are replaced only by direct substitution.

  Every $a before the last declaration is syntax or a faithful definition.
  The last $a is Metamath's native unproved statement encoding, and this
  database contains no $p declaration.
$)

$c
  NTP4VCMatrix NTP4VCRows NTP4VCColumns NTP4VCElts NTP4VCEntry
  NTP4VCRow NTP4VCColumn NTP4VCNumof NTP4VCPermut
  NTP4VCSameShape NTP4VCTranspose
  NTP4VCAllColumnPerm NTP4VCPrefixColumnSorted NTP4VCColumnResult
  NTP4VCSameExceptColumn NTP4VCColumnSortedAt NTP4VCSortColumnPost
  NTP4VCDirectStep NTP4VCDirectFor NTP4VCDirect
  NTP4VCAllRowPerm NTP4VCPrefixRowSorted
  NTP4VCSameExceptRow NTP4VCRowSortedAt NTP4VCSortRowPost
  NTP4VCRowStep NTP4VCRowFor NTP4VCViaTranspose NTP4VCMain
$.

ntp4vc-matrix-syntax
  $a class NTP4VCMatrix $.
ntp4vc-rows-syntax
  $a class ( NTP4VCRows A ) $.
ntp4vc-columns-syntax
  $a class ( NTP4VCColumns A ) $.
ntp4vc-elts-syntax
  $a class ( NTP4VCElts A ) $.
ntp4vc-entry-syntax
  $a class ( NTP4VCEntry A B C ) $.
ntp4vc-row-syntax
  $a class ( NTP4VCRow A B ) $.
ntp4vc-column-syntax
  $a class ( NTP4VCColumn A B ) $.
ntp4vc-numof-syntax
  $a class ( NTP4VCNumof A B C D ) $.

ntp4vc-permut-syntax
  $a wff ( NTP4VCPermut A B C D ) $.
ntp4vc-same-shape-syntax
  $a wff ( NTP4VCSameShape A B ) $.
ntp4vc-transpose-syntax
  $a wff ( NTP4VCTranspose A B ) $.
ntp4vc-all-column-perm-syntax
  $a wff ( NTP4VCAllColumnPerm A B ) $.
ntp4vc-prefix-column-sorted-syntax
  $a wff ( NTP4VCPrefixColumnSorted A B ) $.
ntp4vc-column-result-syntax
  $a wff ( NTP4VCColumnResult A B ) $.
ntp4vc-same-except-column-syntax
  $a wff ( NTP4VCSameExceptColumn A B C ) $.
ntp4vc-column-sorted-at-syntax
  $a wff ( NTP4VCColumnSortedAt A B ) $.
ntp4vc-sort-column-post-syntax
  $a wff ( NTP4VCSortColumnPost A B C ) $.
ntp4vc-direct-step-syntax
  $a wff ( NTP4VCDirectStep A B C ) $.
ntp4vc-direct-for-syntax
  $a wff ( NTP4VCDirectFor A B C ) $.
ntp4vc-direct-syntax
  $a wff ( NTP4VCDirect A ) $.

ntp4vc-all-row-perm-syntax
  $a wff ( NTP4VCAllRowPerm A B C ) $.
ntp4vc-prefix-row-sorted-syntax
  $a wff ( NTP4VCPrefixRowSorted A B C ) $.
ntp4vc-same-except-row-syntax
  $a wff ( NTP4VCSameExceptRow A B C ) $.
ntp4vc-row-sorted-at-syntax
  $a wff ( NTP4VCRowSortedAt A B ) $.
ntp4vc-sort-row-post-syntax
  $a wff ( NTP4VCSortRowPost A B C ) $.
ntp4vc-row-step-syntax
  $a wff ( NTP4VCRowStep A B C D ) $.
ntp4vc-row-for-syntax
  $a wff ( NTP4VCRowFor A B C D ) $.
ntp4vc-via-transpose-syntax
  $a wff ( NTP4VCViaTranspose A ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A ) $.

ntp4vc-matrix-definition $a |- NTP4VCMatrix =
  (
    ( NN0 X. NN0 )
    X.
    ( ZZ ^m ( ZZ X. ZZ ) )
  )
$.

ntp4vc-rows-definition $a |- (
  NTP4VCRows A
) = (
  1st ` ( 1st ` A )
) $.

ntp4vc-columns-definition $a |- (
  NTP4VCColumns A
) = (
  2nd ` ( 1st ` A )
) $.

ntp4vc-elts-definition $a |- (
  NTP4VCElts A
) = (
  2nd ` A
) $.

ntp4vc-entry-definition $a |- (
  NTP4VCEntry A B C
) = (
  ( NTP4VCElts A ) ` <. B , C >.
) $.

${
  $d j A B $.

  ntp4vc-row-definition $a |- (
    NTP4VCRow A B
  ) = (
    j e. ZZ |->
      ( NTP4VCEntry A B j )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-column-definition $a |- (
    NTP4VCColumn A B
  ) = (
    i e. ZZ |->
      ( NTP4VCEntry A i B )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-numof-definition $a |- (
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

  ntp4vc-permut-definition $a |- (
    NTP4VCPermut A B C D
  ) <->
  A. v e. ZZ
    (
      ( NTP4VCNumof A v C D )
      =
      ( NTP4VCNumof B v C D )
    ) $.
$}

ntp4vc-same-shape-definition $a |- (
  NTP4VCSameShape A B
) <->
(
  ( NTP4VCRows A ) = ( NTP4VCRows B )
  /\
  ( NTP4VCColumns A ) = ( NTP4VCColumns B )
) $.

${
  $d i j A B $.

  ntp4vc-transpose-definition $a |- (
    NTP4VCTranspose A B
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i < ( NTP4VCRows B )
          )
          /\
          (
            0 <_ j
            /\
            j < ( NTP4VCColumns B )
          )
        )
        ->
        (
          NTP4VCEntry A i j
        )
        =
        (
          NTP4VCEntry B j i
        )
      ) $.
$}

${
  $d j A B $.

  ntp4vc-all-column-perm-definition $a |- (
    NTP4VCAllColumnPerm A B
  ) <->
  A. j e. ZZ
    (
      (
        0 <_ j
        /\
        j < ( NTP4VCColumns A )
      )
      ->
      (
        NTP4VCPermut
          ( NTP4VCColumn A j )
          ( NTP4VCColumn B j )
          0
          ( NTP4VCRows A )
      )
    ) $.
$}

${
  $d i j k A B $.

  ntp4vc-prefix-column-sorted-definition $a |- (
    NTP4VCPrefixColumnSorted A B
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        (
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
            /\
            (
              0 <_ j
              /\
              j < B
            )
          )
          ->
          (
            ( NTP4VCEntry A i j )
            <_
            ( NTP4VCEntry A k j )
          )
        ) $.
$}

ntp4vc-column-result-definition $a |- (
  NTP4VCColumnResult A B
) <->
(
  ( NTP4VCAllColumnPerm A B )
  /\
  (
    NTP4VCPrefixColumnSorted
      A
      ( NTP4VCColumns A )
  )
) $.

${
  $d i k A B C $.

  ntp4vc-same-except-column-definition $a |- (
    NTP4VCSameExceptColumn A B C
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
          NTP4VCEntry A i k
        )
        =
        (
          NTP4VCEntry B i k
        )
      ) $.
$}

${
  $d i k A B $.

  ntp4vc-column-sorted-at-definition $a |- (
    NTP4VCColumnSortedAt A B
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

ntp4vc-sort-column-post-definition $a |- (
  NTP4VCSortColumnPost A B C
) <->
(
  ( NTP4VCSameExceptColumn A B C )
  /\
  (
    ( NTP4VCColumnSortedAt A C )
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
  $d n A B C $.

  ntp4vc-direct-step-definition $a |- (
    NTP4VCDirectStep A B C
  ) <->
  (
    (
      0 <_ C
      /\
      C < ( NTP4VCColumns B )
    )
    /\
    A. n e. NTP4VCMatrix
      (
        ( NTP4VCSameShape n B )
        ->
        (
          ( NTP4VCSortColumnPost n B C )
          ->
          (
            ( NTP4VCAllColumnPerm n A )
            /\
            (
              NTP4VCPrefixColumnSorted
                n
                ( C + 1 )
            )
          )
        )
      )
  ) $.
$}

${
  $d t A B C $.

  ntp4vc-direct-for-definition $a |- (
    NTP4VCDirectFor A B C
  ) <->
  (
    A. t e. ZZ
      (
        (
          (
            (
              0 <_ t
              /\
              t <_ C
            )
            /\
            ( NTP4VCAllColumnPerm B A )
          )
          /\
          ( NTP4VCPrefixColumnSorted B t )
        )
        ->
        ( NTP4VCDirectStep A B t )
      )
    /\
    (
      (
        ( NTP4VCAllColumnPerm B A )
        /\
        (
          NTP4VCPrefixColumnSorted
            B
            ( C + 1 )
        )
      )
      ->
      ( NTP4VCColumnResult B A )
    )
  ) $.
$}

${
  $d m A $.

  ntp4vc-direct-definition $a |- (
    NTP4VCDirect A
  ) <->
  (
    (
      0 <_
      (
        ( ( NTP4VCColumns A ) - 1 )
        +
        1
      )
      ->
      (
        (
          ( NTP4VCAllColumnPerm A A )
          /\
          ( NTP4VCPrefixColumnSorted A 0 )
        )
        /\
        A. m e. NTP4VCMatrix
          (
            ( NTP4VCSameShape m A )
            ->
            (
              NTP4VCDirectFor
                A
                m
                ( ( NTP4VCColumns A ) - 1 )
            )
          )
      )
    )
    /\
    (
      (
        (
          ( NTP4VCColumns A ) - 1
        )
        +
        1
      )
      <
      0
      ->
      ( NTP4VCColumnResult A A )
    )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-all-row-perm-definition $a |- (
    NTP4VCAllRowPerm A B C
  ) <->
  A. j e. ZZ
    (
      (
        0 <_ j
        /\
        j < C
      )
      ->
      (
        NTP4VCPermut
          ( NTP4VCRow A j )
          ( NTP4VCColumn B j )
          0
          C
      )
    ) $.
$}

${
  $d i j k A B C $.

  ntp4vc-prefix-row-sorted-definition $a |- (
    NTP4VCPrefixRowSorted A B C
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        (
          (
            (
              (
                0 <_ i
                /\
                i <_ k
              )
              /\
              k < B
            )
            /\
            (
              0 <_ j
              /\
              j < C
            )
          )
          ->
          (
            ( NTP4VCEntry A j i )
            <_
            ( NTP4VCEntry A j k )
          )
        ) $.
$}

${
  $d j k A B C $.

  ntp4vc-same-except-row-definition $a |- (
    NTP4VCSameExceptRow A B C
  ) <->
  A. j e. ZZ
    A. k e. ZZ
      (
        (
          (
            (
              0 <_ j
              /\
              j < ( NTP4VCRows A )
            )
            /\
            (
              0 <_ k
              /\
              k < ( NTP4VCColumns A )
            )
          )
          /\
          -. j = C
        )
        ->
        (
          NTP4VCEntry A j k
        )
        =
        (
          NTP4VCEntry B j k
        )
      ) $.
$}

${
  $d j k A B $.

  ntp4vc-row-sorted-at-definition $a |- (
    NTP4VCRowSortedAt A B
  ) <->
  A. j e. ZZ
    A. k e. ZZ
      (
        (
          (
            0 <_ j
            /\
            j <_ k
          )
          /\
          k < ( NTP4VCColumns A )
        )
        ->
        (
          ( NTP4VCEntry A B j )
          <_
          ( NTP4VCEntry A B k )
        )
      ) $.
$}

ntp4vc-sort-row-post-definition $a |- (
  NTP4VCSortRowPost A B C
) <->
(
  ( NTP4VCSameExceptRow A B C )
  /\
  (
    ( NTP4VCRowSortedAt A C )
    /\
    (
      NTP4VCPermut
        ( NTP4VCRow A C )
        ( NTP4VCRow B C )
        0
        ( NTP4VCColumns A )
    )
  )
) $.

${
  $d n A B C D $.

  ntp4vc-row-step-definition $a |- (
    NTP4VCRowStep A B C D
  ) <->
  (
    (
      0 <_ D
      /\
      D < ( NTP4VCRows B )
    )
    /\
    A. n e. NTP4VCMatrix
      (
        ( NTP4VCSameShape n B )
        ->
        (
          ( NTP4VCSortRowPost n B D )
          ->
          (
            ( NTP4VCAllRowPerm n A C )
            /\
            (
              NTP4VCPrefixRowSorted
                n
                C
                ( D + 1 )
            )
          )
        )
      )
  ) $.
$}

${
  $d n t A B C D $.

  ntp4vc-row-for-definition $a |- (
    NTP4VCRowFor A B C D
  ) <->
  (
    A. t e. ZZ
      (
        (
          (
            (
              0 <_ t
              /\
              t <_ D
            )
            /\
            ( NTP4VCAllRowPerm B A C )
          )
          /\
          ( NTP4VCPrefixRowSorted B C t )
        )
        ->
        ( NTP4VCRowStep A B C t )
      )
    /\
    (
      (
        ( NTP4VCAllRowPerm B A C )
        /\
        (
          NTP4VCPrefixRowSorted
            B
            C
            ( D + 1 )
        )
      )
      ->
      (
        ( NTP4VCRows B ) = ( NTP4VCColumns B )
        /\
        A. n e. NTP4VCMatrix
          (
            ( NTP4VCSameShape n B )
            ->
            (
              ( NTP4VCTranspose B n )
              ->
              ( NTP4VCColumnResult n A )
            )
          )
      )
    )
  ) $.
$}

${
  $d m n A $.

  ntp4vc-via-transpose-definition $a |- (
    NTP4VCViaTranspose A
  ) <->
  (
    ( NTP4VCRows A ) = ( NTP4VCColumns A )
    /\
    A. m e. NTP4VCMatrix
      (
        ( NTP4VCSameShape m A )
        ->
        (
          ( NTP4VCTranspose A m )
          ->
          (
            (
              0 <_
              (
                ( ( NTP4VCColumns m ) - 1 )
                +
                1
              )
              ->
              (
                (
                  (
                    NTP4VCAllRowPerm
                      m
                      A
                      ( NTP4VCRows A )
                  )
                  /\
                  (
                    NTP4VCPrefixRowSorted
                      m
                      ( NTP4VCRows A )
                      0
                  )
                )
                /\
                A. n e. NTP4VCMatrix
                  (
                    ( NTP4VCSameShape n m )
                    ->
                    (
                      NTP4VCRowFor
                        A
                        n
                        ( NTP4VCRows A )
                        ( ( NTP4VCColumns m ) - 1 )
                    )
                  )
              )
            )
            /\
            (
              (
                (
                  ( NTP4VCColumns m ) - 1
                )
                +
                1
              )
              <
              0
              ->
              (
                ( NTP4VCRows m ) = ( NTP4VCColumns m )
                /\
                A. n e. NTP4VCMatrix
                  (
                    ( NTP4VCSameShape n m )
                    ->
                    (
                      ( NTP4VCTranspose m n )
                      ->
                      ( NTP4VCColumnResult n A )
                    )
                  )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d o r A $.

  ntp4vc-main-definition $a |- (
    NTP4VCMain A
  ) <->
  (
    E. r e. { 0 , 1 }
      (
        r = 1
        \/
        ( NTP4VCRows A ) = ( NTP4VCColumns A )
      )
    /\
    A. o e. { 0 , 1 }
      (
        (
          o = 1
          \/
          ( NTP4VCRows A ) = ( NTP4VCColumns A )
        )
        ->
        (
          (
            o = 1
            /\
            ( NTP4VCDirect A )
          )
          \/
          (
            o = 0
            /\
            ( NTP4VCViaTranspose A )
          )
        )
      )
  ) $.
$}

ntp4vc-pearl-verifythis-2021-shearsort-sort-all-columns-vc $a |-
  A. m e. NTP4VCMatrix
    ( NTP4VCMain m )
$.
