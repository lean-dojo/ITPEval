$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_update_aux_complexityqtvc: the cumulative-tree
  point-update auxiliary verification condition preserves updated half-open
  range sums and tree bounds while bounding the instrumented credit increase
  by tree depth. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, and NTP4VCSum reproduce Int.toNat, totalized list
  lookup with default zero, List.set, and finite summation over a half-open
  interval. Every sum use admitted by is_tree_for is within the source bounds,
  where NTP4VCSum is definitionally equivalent to ArraySum.sum.

  An indexes record is represented by the full product
  ZZ X. ( ZZ X. ZZ ). NTP4VCLeaf and NTP4VCNode are injective disjoint tagged
  constructors. Constructor closure, exhaustiveness, and structural induction
  make T exactly the source type of finite cumulative trees, without a finite
  approximation or extraneous non-well-founded values. NTP4VCIndexes,
  NTP4VCLow, NTP4VCHigh, and NTP4VCISum are the source record projections.

  R and D represent is_tree_for and depth. Their complete leaf and node
  equations below are the source recursive definitions. Why3 computer
  division by the positive integer 2 is represented by the floor of the
  rational quotient; is_tree_for makes both endpoints nonnegative, so this
  agrees with the source operation. NTP4VCChild expands the source match that
  tests whether a subtree is an immediate child. The remaining predicates are
  biconditional factorizations of the leaf result, recursive-call result,
  rebuilt-node result, and the two branches of the proposition-valued
  conditional.

  Expanding all definitions recovers every source tree, integer-list, and
  integer domain; all three assumptions; the original internal universal
  scopes of c1 and the updated subtree; and the complete leaf and node
  conclusions. The final declaration is Metamath's native unproved $a
  statement encoding; every preceding $a is syntax or a faithful definition
  required to state it, and this database contains no $p proof declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCIndexes
  NTP4VCLow NTP4VCHigh NTP4VCISum NTP4VCMax
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCSum
  NTP4VCIsIndexes NTP4VCIsTree NTP4VCChild
  NTP4VCUpdatedIndexes NTP4VCRecursiveResult NTP4VCRebuiltResult
  NTP4VCLeafOutcome NTP4VCLeftBranch NTP4VCRightBranch
  NTP4VCNodeOutcome
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
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.
ntp4vc-updated-indexes-syntax
  $a class ( NTP4VCUpdatedIndexes A B C D ) $.

ntp4vc-is-indexes-syntax
  $a wff ( NTP4VCIsIndexes A B C D ) $.
ntp4vc-is-tree-syntax
  $a wff ( NTP4VCIsTree A B C D E ) $.
ntp4vc-child-syntax
  $a wff ( NTP4VCChild A B ) $.
ntp4vc-recursive-result-syntax
  $a wff ( NTP4VCRecursiveResult A B C D E F G H I ) $.
ntp4vc-rebuilt-result-syntax
  $a wff ( NTP4VCRebuiltResult A B C D E F G H I ) $.
ntp4vc-leaf-outcome-syntax
  $a wff ( NTP4VCLeafOutcome A B C D E F G H ) $.
ntp4vc-left-branch-syntax
  $a wff ( NTP4VCLeftBranch A B C D E F G H I J ) $.
ntp4vc-right-branch-syntax
  $a wff ( NTP4VCRightBranch A B C D E F G H I J ) $.
ntp4vc-node-outcome-syntax
  $a wff ( NTP4VCNodeOutcome A B C D E F G H I J ) $.

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

ntp4vc-max-definition $a |- (
  NTP4VCMax A B
) = if (
  A <_ B ,
  B ,
  A
) $.

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

  ntp4vc-set-definition $a |- (
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
  $d i l r A B $.

  ntp4vc-child-definition $a |- (
    NTP4VCChild A B
  ) <->
  E. i e. ( ZZ X. ( ZZ X. ZZ ) )
    E. l e. _V E. r e. _V
      (
        A = ( NTP4VCNode i l r )
        /\
        (
          l = B
          \/
          r = B
        )
      ) $.
$}

ntp4vc-updated-indexes-definition $a |- (
  NTP4VCUpdatedIndexes A B C D
) = <.
  ( NTP4VCLow A ) ,
  <.
    ( NTP4VCHigh A ) ,
    (
      ( NTP4VCISum A )
      +
      (
        D
        -
        ( NTP4VCAt B C )
      )
    )
  >.
>. $.

ntp4vc-recursive-result-definition $a |- (
  NTP4VCRecursiveResult A B C D E F G H I
) <->
(
  (
    I - ( H + 1 )
  )
  <_
  ( B ` C )
  /\
  (
    ( NTP4VCLow ( NTP4VCIndexes D ) )
    =
    ( NTP4VCLow ( NTP4VCIndexes C ) )
    /\
    (
      ( NTP4VCHigh ( NTP4VCIndexes D ) )
      =
      ( NTP4VCHigh ( NTP4VCIndexes C ) )
      /\
      (
        NTP4VCIsTree
          A D
          ( NTP4VCSet E F G )
          ( NTP4VCLow ( NTP4VCIndexes D ) )
          ( NTP4VCHigh ( NTP4VCIndexes D ) )
      )
    )
  )
) $.

ntp4vc-rebuilt-result-definition $a |- (
  NTP4VCRebuiltResult A B C D E F G H I
) <->
(
  ( I - H ) <_ ( B ` C )
  /\
  (
    ( NTP4VCLow ( NTP4VCIndexes D ) )
    =
    ( NTP4VCLow ( NTP4VCIndexes C ) )
    /\
    (
      ( NTP4VCHigh ( NTP4VCIndexes D ) )
      =
      ( NTP4VCHigh ( NTP4VCIndexes C ) )
      /\
      (
        NTP4VCIsTree
          A D
          ( NTP4VCSet E F G )
          ( NTP4VCLow ( NTP4VCIndexes D ) )
          ( NTP4VCHigh ( NTP4VCIndexes D ) )
      )
    )
  )
) $.

ntp4vc-leaf-outcome-definition $a |- (
  NTP4VCLeafOutcome A B C D E F G H
) <->
(
  (
    ( ( H + 1 ) - H ) <_ ( B ` C )
    /\
    (
      ( G - ( NTP4VCISum D ) )
      =
      ( G - ( NTP4VCAt E F ) )
    )
  )
  /\
  (
    (
      NTP4VCLow
        (
          NTP4VCIndexes
            (
              NTP4VCLeaf
                <.
                  ( NTP4VCLow D ) ,
                  <. ( NTP4VCHigh D ) , G >.
                >.
            )
        )
    )
    =
    ( NTP4VCLow ( NTP4VCIndexes C ) )
    /\
    (
      (
        NTP4VCHigh
          (
            NTP4VCIndexes
              (
                NTP4VCLeaf
                  <.
                    ( NTP4VCLow D ) ,
                    <. ( NTP4VCHigh D ) , G >.
                  >.
              )
          )
      )
      =
      ( NTP4VCHigh ( NTP4VCIndexes C ) )
      /\
      (
        NTP4VCIsTree
          A
          (
            NTP4VCLeaf
              <.
                ( NTP4VCLow D ) ,
                <. ( NTP4VCHigh D ) , G >.
              >.
          )
          ( NTP4VCSet E F G )
          (
            NTP4VCLow
              (
                NTP4VCIndexes
                  (
                    NTP4VCLeaf
                      <.
                        ( NTP4VCLow D ) ,
                        <. ( NTP4VCHigh D ) , G >.
                      >.
                  )
              )
          )
          (
            NTP4VCHigh
              (
                NTP4VCIndexes
                  (
                    NTP4VCLeaf
                      <.
                        ( NTP4VCLow D ) ,
                        <. ( NTP4VCHigh D ) , G >.
                      >.
                  )
              )
          )
      )
    )
  )
) $.

${
  $d q s A B C D E F G H I J $.

  ntp4vc-left-branch-definition $a |- (
    NTP4VCLeftBranch A B C D E F G H I J
  ) <->
  (
    (
      ( NTP4VCChild C E )
      /\
      (
        (
          NTP4VCIsTree
            A E G
            ( NTP4VCLow ( NTP4VCIndexes E ) )
            ( NTP4VCHigh ( NTP4VCIndexes E ) )
        )
        /\
        (
          ( NTP4VCLow ( NTP4VCIndexes E ) ) <_ H
          /\
          H < ( NTP4VCHigh ( NTP4VCIndexes E ) )
        )
      )
    )
    /\
    A. q e. ZZ A. s e. T
      (
        NTP4VCRecursiveResult
          A B E s G H I J q
        ->
        (
          NTP4VCRebuiltResult
            A B C
            (
              NTP4VCNode
                ( NTP4VCUpdatedIndexes D G H I )
                s F
            )
            G H I J q
        )
      )
  ) $.
$}

${
  $d q s A B C D E F G H I J $.

  ntp4vc-right-branch-definition $a |- (
    NTP4VCRightBranch A B C D E F G H I J
  ) <->
  (
    (
      ( NTP4VCChild C F )
      /\
      (
        (
          NTP4VCIsTree
            A F G
            ( NTP4VCLow ( NTP4VCIndexes F ) )
            ( NTP4VCHigh ( NTP4VCIndexes F ) )
        )
        /\
        (
          ( NTP4VCLow ( NTP4VCIndexes F ) ) <_ H
          /\
          H < ( NTP4VCHigh ( NTP4VCIndexes F ) )
        )
      )
    )
    /\
    A. q e. ZZ A. s e. T
      (
        NTP4VCRecursiveResult
          A B F s G H I J q
        ->
        (
          NTP4VCRebuiltResult
            A B C
            (
              NTP4VCNode
                ( NTP4VCUpdatedIndexes D G H I )
                E s
            )
            G H I J q
        )
      )
  ) $.
$}

ntp4vc-node-outcome-definition $a |- (
  NTP4VCNodeOutcome A B C D E F G H I J
) <->
(
  (
    H < ( NTP4VCHigh ( NTP4VCIndexes E ) )
    ->
    (
      NTP4VCLeftBranch
        A B C D E F G H I J
    )
  )
  /\
  (
    -.
    H < ( NTP4VCHigh ( NTP4VCIndexes E ) )
    ->
    (
      NTP4VCRightBranch
        A B C D E F G H I J
    )
  )
) $.

${
  $d a c i l q r s t v
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

  $( Complete recursive source definitions of is_tree_for and depth. $)
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
                        (
                          |_ `
                          (
                            ( j + k )
                            /
                            2
                          )
                        )
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

  ntp4vc-depth-function $e |- D e. ( ZZ ^m T ) $.

  ntp4vc-depth-leaf-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      ( D ` ( NTP4VCLeaf i ) ) = 1 $.

  ntp4vc-depth-node-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. l e. T A. r e. T
        (
          D ` ( NTP4VCNode i l r )
        )
        =
        (
          1
          +
          (
            NTP4VCMax
              ( D ` l )
              ( D ` r )
          )
        ) $.

  $( Source theorem parameters t, a, i, v, and c. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-a-list $e |- B e. Word ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-v-integer $e |- E e. ZZ $.
  ntp4vc-c-integer $e |- F e. ZZ $.

  $( Source facts fact0 through fact2. $)
  ntp4vc-fact0 $e |- (
    NTP4VCIsTree
      R A B
      ( NTP4VCLow ( NTP4VCIndexes A ) )
      ( NTP4VCHigh ( NTP4VCIndexes A ) )
  ) $.

  ntp4vc-fact1 $e |-
    ( NTP4VCLow ( NTP4VCIndexes A ) ) <_ C $.

  ntp4vc-fact2 $e |-
    C < ( NTP4VCHigh ( NTP4VCIndexes A ) ) $.

  ntp4vc-pearl-sumrange-cumulative-tree-update-aux-complexity-vc $a |- (
    E. i e. ( ZZ X. ( ZZ X. ZZ ) )
      (
        A = ( NTP4VCLeaf i )
        /\
        (
          NTP4VCLeafOutcome
            R D A i B C E F
        )
      )
    \/
    E. i e. ( ZZ X. ( ZZ X. ZZ ) )
      E. l e. T E. r e. T
        (
          A = ( NTP4VCNode i l r )
          /\
          (
            NTP4VCNodeOutcome
              R D A i l r B C E F
          )
        )
  ) $.
$}
