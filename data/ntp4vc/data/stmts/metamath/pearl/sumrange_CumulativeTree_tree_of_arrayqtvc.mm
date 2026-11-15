$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_tree_of_arrayqtvc: the cumulative-tree
  construction verification condition preserves decreasing recursive ranges
  and establishes the exact range-sum tree specification. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat,
  NTP4VCAt, and NTP4VCSum reproduce Int.toNat, totalized list lookup with
  default zero, and the finite sum over a half-open interval. Every lookup and
  sum used by the VC is under the source bounds, where these definitions agree
  with Why3 arrays and ArraySum.sum.

  An indexes record is represented by the full product
  ZZ X. ( ZZ X. ZZ ). NTP4VCLeaf and NTP4VCNode are injective disjoint tagged
  constructors. Constructor closure, exhaustiveness, and structural induction
  make T exactly the source type of finite cumulative trees, without a finite
  approximation or extraneous non-well-founded values. NTP4VCIndexes,
  NTP4VCLow, NTP4VCHigh, and NTP4VCISum are the source record projections.

  R represents is_tree_for, and its complete leaf and node equations below are
  the source recursive definition. Why3 computer division by the positive
  integer 2 is represented by the floor of the rational quotient. The source
  assumptions make i+j nonnegative, so this is also the division rendered by
  the Lean and Isabelle exports. NTP4VCSplit is the complete pair of variant
  and recursive-call obligations for the midpoint branch. NTP4VCBuild is
  biconditional to the source conditional result construction, retaining both
  internally existentially quantified subtrees.

  Proposition-valued conditionals are represented by their equivalent guarded
  true and false implications. Expanding all definitions recovers every source
  list, integer, record, and tree domain; all three assumptions; the base and
  recursive branch obligations; both existential subtree witnesses; and the
  universal result postcondition. The final declaration is Metamath's native
  unproved $a statement encoding; every preceding $a is syntax or a faithful
  definition required to state it, and this database contains no $p proof
  declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCIndexes
  NTP4VCLow NTP4VCHigh NTP4VCISum
  NTP4VCToNat NTP4VCAt NTP4VCSum NTP4VCMid
  NTP4VCIsIndexes NTP4VCIsTree NTP4VCSplit NTP4VCBuild
$.

ntp4vc-leaf-syntax
  $a class ( NTP4VCLeaf A ) $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-indexes-syntax
  $a class ( NTP4VCIndexes A ) $.
ntp4vc-low-syntax
  $a class ( NTP4VCLow A ) $.
ntp4vc-high-syntax
  $a class ( NTP4VCHigh A ) $.
ntp4vc-isum-syntax
  $a class ( NTP4VCISum A ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.
ntp4vc-mid-syntax
  $a class ( NTP4VCMid A B ) $.

ntp4vc-is-indexes-syntax
  $a wff ( NTP4VCIsIndexes A B C D ) $.
ntp4vc-is-tree-syntax
  $a wff ( NTP4VCIsTree A B C D E ) $.
ntp4vc-split-syntax
  $a wff ( NTP4VCSplit A B C D E ) $.
ntp4vc-build-syntax
  $a wff ( NTP4VCBuild A B C D E F ) $.

ntp4vc-leaf-definition $a |- (
  NTP4VCLeaf A
) = <. 0 , A >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-indexes-definition $a |- (
  NTP4VCIndexes A
) = if (
  ( 1st ` A ) = 0 ,
  ( 2nd ` A ) ,
  ( 1st ` ( 2nd ` A ) )
) $.

ntp4vc-low-definition $a |- (
  NTP4VCLow A
) = ( 1st ` A ) $.

ntp4vc-high-definition $a |- (
  NTP4VCHigh A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-isum-definition $a |- (
  NTP4VCISum A
) = ( 2nd ` ( 2nd ` A ) ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-sum-definition $a |- (
    NTP4VCSum A B C
  ) = sum_ k e.
    (
      ( NTP4VCToNat B )
      ..^
      ( NTP4VCToNat C )
    )
    ( NTP4VCAt A k ) $.
$}

ntp4vc-mid-definition $a |- (
  NTP4VCMid A B
) = (
  |_ `
  (
    ( A + B )
    /
    2
  )
) $.

ntp4vc-is-indexes-definition $a |- (
  NTP4VCIsIndexes A B C D
) <->
(
  ( NTP4VCLow A ) = C
  /\
  (
    ( NTP4VCHigh A ) = D
    /\
    (
      (
        0 <_ C
        /\
        (
          C < D
          /\
          D <_ ( # ` B )
        )
      )
      /\
      ( NTP4VCISum A ) = ( NTP4VCSum B C D )
    )
  )
) $.

ntp4vc-is-tree-definition $a |- (
  NTP4VCIsTree A B C D E
) <->
<. B , <. C , <. D , E >. >. >. e. A $.

${
  $d l A B C D E $.

  ntp4vc-split-definition $a |- (
    NTP4VCSplit A B C D E
  ) <->
  (
    (
      (
        0 <_ ( E - D )
        /\
        (
          ( ( NTP4VCMid D E ) - D )
          <
          ( E - D )
        )
      )
      /\
      (
        0 <_ D
        /\
        (
          D < ( NTP4VCMid D E )
          /\
          ( NTP4VCMid D E ) <_ ( # ` C )
        )
      )
    )
    /\
    A. l e. B
      (
        (
          NTP4VCIsTree
            A l C D
            ( NTP4VCMid D E )
        )
        ->
        (
          (
            0 <_ ( E - D )
            /\
            (
              ( E - ( NTP4VCMid D E ) )
              <
              ( E - D )
            )
          )
          /\
          (
            0 <_ ( NTP4VCMid D E )
            /\
            (
              ( NTP4VCMid D E ) < E
              /\
              E <_ ( # ` C )
            )
          )
        )
      )
  ) $.
$}

${
  $d l r A B C D E F $.

  ntp4vc-build-definition $a |- (
    NTP4VCBuild A B C D E F
  ) <->
  (
    (
      ( D + 1 ) = E
      ->
      F =
      (
        NTP4VCLeaf
        <.
          D ,
          <.
            E ,
            ( NTP4VCAt C D )
          >.
        >.
      )
    )
    /\
    (
      -. ( D + 1 ) = E
      ->
      E. l e. B
        (
          (
            NTP4VCIsTree
              A l C D
              ( NTP4VCMid D E )
          )
          /\
          E. r e. B
            (
              (
                NTP4VCIsTree
                  A r C
                  ( NTP4VCMid D E )
                  E
              )
              /\
              F =
              (
                NTP4VCNode
                  <.
                    D ,
                    <.
                      E ,
                      (
                        ( NTP4VCISum ( NTP4VCIndexes l ) )
                        +
                        ( NTP4VCISum ( NTP4VCIndexes r ) )
                      )
                    >.
                  >.
                  l
                  r
              )
            )
        )
    )
  ) $.
$}

${
  $d a i j l r s t
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite source tree carrier over the full indexes record product. $)
  ntp4vc-tree-leaf-closure $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      ( NTP4VCLeaf i ) e. T $.

  ntp4vc-tree-node-closure $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. l e. T A. r e. T
        ( NTP4VCNode i l r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      E. i e. ( ZZ X. ( ZZ X. ZZ ) )
        t = ( NTP4VCLeaf i )
      \/
      E. i e. ( ZZ X. ( ZZ X. ZZ ) )
        E. l e. T E. r e. T
          t = ( NTP4VCNode i l r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        A. i e. ( ZZ X. ( ZZ X. ZZ ) )
          ( NTP4VCLeaf i ) e. s
        /\
        A. i e. ( ZZ X. ( ZZ X. ZZ ) )
          A. l e. T A. r e. T
            (
              (
                l e. s
                /\
                r e. s
              )
              ->
              ( NTP4VCNode i l r ) e. s
            )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source definition of is_tree_for. $)
  ntp4vc-is-tree-relation $e |- R C_
    (
      T
      X.
      (
        ( Word ZZ )
        X.
        ( ZZ X. ZZ )
      )
    ) $.

  ntp4vc-is-tree-leaf-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. a e. Word ZZ A. j e. ZZ A. k e. ZZ
        (
          NTP4VCIsTree R ( NTP4VCLeaf i ) a j k
          <->
          (
            ( NTP4VCIsIndexes i a j k )
            /\
            k = ( j + 1 )
          )
        ) $.

  ntp4vc-is-tree-node-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. l e. T A. r e. T
        A. a e. Word ZZ A. j e. ZZ A. k e. ZZ
          (
            NTP4VCIsTree R ( NTP4VCNode i l r ) a j k
            <->
            (
              ( NTP4VCIsIndexes i a j k )
              /\
              (
                j = ( NTP4VCLow ( NTP4VCIndexes l ) )
                /\
                (
                  k = ( NTP4VCHigh ( NTP4VCIndexes r ) )
                  /\
                  (
                    (
                      NTP4VCHigh ( NTP4VCIndexes l )
                    )
                    =
                    (
                      NTP4VCLow ( NTP4VCIndexes r )
                    )
                    /\
                    (
                      (
                        j < ( NTP4VCHigh ( NTP4VCIndexes l ) )
                        /\
                        ( NTP4VCHigh ( NTP4VCIndexes l ) ) < k
                      )
                      /\
                      (
                        (
                          NTP4VCHigh ( NTP4VCIndexes l )
                        )
                        =
                        ( NTP4VCMid j k )
                        /\
                        (
                          (
                            NTP4VCIsTree
                              R l a j
                              ( NTP4VCHigh ( NTP4VCIndexes l ) )
                          )
                          /\
                          (
                            NTP4VCIsTree
                              R r a
                              ( NTP4VCHigh ( NTP4VCIndexes l ) )
                              k
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          ) $.

  $( Source theorem parameters a, i, and j. $)
  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-i-integer $e |- B e. ZZ $.
  ntp4vc-j-integer $e |- C e. ZZ $.

  $( Source assumptions fact0 through fact2. $)
  ntp4vc-fact0 $e |- 0 <_ B $.
  ntp4vc-fact1 $e |- B < C $.
  ntp4vc-fact2 $e |- C <_ ( # ` A ) $.

  ntp4vc-pearl-sumrange-cumulative-tree-tree-of-array-vc $a |- (
    (
      (
        ( B + 1 ) = C
        ->
        (
          0 <_ B
          /\
          B < ( # ` A )
        )
      )
      /\
      (
        -. ( B + 1 ) = C
        ->
        (
          -. 2 = 0
          /\
          ( NTP4VCSplit R T A B C )
        )
      )
    )
    /\
    A. t e. T
      (
        ( NTP4VCBuild R T A B C t )
        ->
        ( NTP4VCIsTree R t A B C )
      )
  ) $.
$}
