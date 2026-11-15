$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_update_auxqtvc: the cumulative-tree point-update
  auxiliary verification condition preserves the updated half-open range sum
  and the tree's interval bounds. This file contains no proof.
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

  R represents is_tree_for, and its complete leaf and node equations below are
  the source recursive definition. Why3 computer division by the positive
  integer 2 is represented by the floor of the rational quotient;
  is_tree_for makes both endpoints nonnegative, so this agrees with the source
  operation. NTP4VCChild expands the repeated source match testing whether a
  tree is an immediate child. The remaining predicates are biconditional
  factorizations of the recursive-call result, rebuilt-tree postcondition,
  leaf case, node call precondition, and node computation premise.

  Proposition-valued conditionals are represented by equivalent guarded
  branches or a guarded disjunction. Expanding all definitions recovers every
  source tree, integer-list, and integer domain; all three assumptions; the
  internal existential scope of the recursively updated subtree; the universal
  scopes of t' and delta; and both conjuncts of the complete conclusion. The
  final declaration is Metamath's native unproved $a statement encoding;
  every preceding $a is syntax or a faithful definition required to state it,
  and this database contains no $p proof declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCIndexes
  NTP4VCLow NTP4VCHigh NTP4VCISum
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCSum
  NTP4VCIsIndexes NTP4VCIsTree NTP4VCChild
  NTP4VCUpdatedIndexes NTP4VCRecursiveResult NTP4VCFinalResult
  NTP4VCLeafOutcome NTP4VCNodeReady NTP4VCNodePremise NTP4VCNodeOutcome
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
  $a wff ( NTP4VCRecursiveResult A B C D E F ) $.
ntp4vc-final-result-syntax
  $a wff ( NTP4VCFinalResult A B C D E F G ) $.
ntp4vc-leaf-outcome-syntax
  $a wff ( NTP4VCLeafOutcome A B C D E F ) $.
ntp4vc-node-ready-syntax
  $a wff ( NTP4VCNodeReady A B C D E F ) $.
ntp4vc-node-premise-syntax
  $a wff ( NTP4VCNodePremise A B C D E F G H I ) $.
ntp4vc-node-outcome-syntax
  $a wff ( NTP4VCNodeOutcome A B C D E F G H ) $.

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
  NTP4VCRecursiveResult A B C D E F
) <->
(
  ( NTP4VCLow ( NTP4VCIndexes C ) )
  =
  ( NTP4VCLow ( NTP4VCIndexes B ) )
  /\
  (
    ( NTP4VCHigh ( NTP4VCIndexes C ) )
    =
    ( NTP4VCHigh ( NTP4VCIndexes B ) )
    /\
    (
      NTP4VCIsTree
        A C
        ( NTP4VCSet D E F )
        ( NTP4VCLow ( NTP4VCIndexes C ) )
        ( NTP4VCHigh ( NTP4VCIndexes C ) )
    )
  )
) $.

ntp4vc-final-result-definition $a |- (
  NTP4VCFinalResult A B C D E F G
) <->
(
  G = ( F - ( NTP4VCAt D E ) )
  /\
  (
    ( NTP4VCLow ( NTP4VCIndexes C ) )
    =
    ( NTP4VCLow ( NTP4VCIndexes B ) )
    /\
    (
      ( NTP4VCHigh ( NTP4VCIndexes C ) )
      =
      ( NTP4VCHigh ( NTP4VCIndexes B ) )
      /\
      (
        NTP4VCIsTree
          A C
          ( NTP4VCSet D E F )
          ( NTP4VCLow ( NTP4VCIndexes C ) )
          ( NTP4VCHigh ( NTP4VCIndexes C ) )
      )
    )
  )
) $.

${
  $d q s A B C D E F $.

  ntp4vc-leaf-outcome-definition $a |- (
    NTP4VCLeafOutcome A B C D E F
  ) <->
  A. s e. T A. q e. ZZ
    (
      (
        s =
        (
          NTP4VCLeaf
            <.
              ( NTP4VCLow C ) ,
              <. ( NTP4VCHigh C ) , F >.
            >.
        )
        /\
        q = ( F - ( NTP4VCISum C ) )
      )
      ->
      ( NTP4VCFinalResult A B s D E F q )
    ) $.
$}

ntp4vc-node-ready-definition $a |- (
  NTP4VCNodeReady A B C D E F
) <->
(
  (
    F < ( NTP4VCHigh ( NTP4VCIndexes C ) )
    ->
    (
      ( NTP4VCChild B C )
      /\
      (
        (
          NTP4VCIsTree
            A C E
            ( NTP4VCLow ( NTP4VCIndexes C ) )
            ( NTP4VCHigh ( NTP4VCIndexes C ) )
        )
        /\
        (
          ( NTP4VCLow ( NTP4VCIndexes C ) ) <_ F
          /\
          F < ( NTP4VCHigh ( NTP4VCIndexes C ) )
        )
      )
    )
  )
  /\
  (
    -.
    F < ( NTP4VCHigh ( NTP4VCIndexes C ) )
    ->
    (
      ( NTP4VCChild B D )
      /\
      (
        (
          NTP4VCIsTree
            A D E
            ( NTP4VCLow ( NTP4VCIndexes D ) )
            ( NTP4VCHigh ( NTP4VCIndexes D ) )
        )
        /\
        (
          ( NTP4VCLow ( NTP4VCIndexes D ) ) <_ F
          /\
          F < ( NTP4VCHigh ( NTP4VCIndexes D ) )
        )
      )
    )
  )
) $.

${
  $d u A B C D E F G H I $.

  ntp4vc-node-premise-definition $a |- (
    NTP4VCNodePremise A B C D E F G H I
  ) <->
  (
    (
      F < ( NTP4VCHigh ( NTP4VCIndexes C ) )
      /\
      E. u e. T
        (
          ( NTP4VCRecursiveResult A C u E F G )
          /\
          (
            H =
            (
              NTP4VCNode
                ( NTP4VCUpdatedIndexes B E F G )
                u D
            )
            /\
            I = ( G - ( NTP4VCAt E F ) )
          )
        )
    )
    \/
    (
      -.
      F < ( NTP4VCHigh ( NTP4VCIndexes C ) )
      /\
      E. u e. T
        (
          ( NTP4VCRecursiveResult A D u E F G )
          /\
          (
            H =
            (
              NTP4VCNode
                ( NTP4VCUpdatedIndexes B E F G )
                C u
            )
            /\
            I = ( G - ( NTP4VCAt E F ) )
          )
        )
    )
  ) $.
$}

${
  $d q s A B C D E F G H $.

  ntp4vc-node-outcome-definition $a |- (
    NTP4VCNodeOutcome A B C D E F G H
  ) <->
  (
    ( NTP4VCNodeReady A B D E F G )
    /\
    A. s e. T A. q e. ZZ
      (
        ( NTP4VCNodePremise A C D E F G H s q )
        ->
        ( NTP4VCFinalResult A B s F G H q )
      )
  ) $.
$}

${
  $d a i l q r s t u v
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

  $( Source theorem parameters A=t, B=a, C=i, and D=v. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-a-list $e |- B e. Word ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-v-integer $e |- D e. ZZ $.

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

  ntp4vc-pearl-sumrange-cumulative-tree-update-aux-vc $a |- (
    E. i e. ( ZZ X. ( ZZ X. ZZ ) )
      (
        A = ( NTP4VCLeaf i )
        /\
        ( NTP4VCLeafOutcome R A i B C D )
      )
    \/
    E. i e. ( ZZ X. ( ZZ X. ZZ ) )
      E. l e. T E. r e. T
        (
          A = ( NTP4VCNode i l r )
          /\
          ( NTP4VCNodeOutcome R A i l r B C D )
        )
  ) $.
$}
