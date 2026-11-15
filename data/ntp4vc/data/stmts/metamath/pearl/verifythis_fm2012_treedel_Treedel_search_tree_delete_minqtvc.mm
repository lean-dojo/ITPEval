$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc
  (ntp4vc__metamath__pearl/verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc):
  the generated verification condition for deleting the minimum node from a
  nonempty pointer-based binary tree, retaining the exact branch, traversal,
  memory-update, tree-shape, root, data-frame, and inorder obligations. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited location carrier, E is null, and
  NTP4VCTDNodeType U is the exact record type with left and right locations
  and integer data. NTP4VCTDMemoryType U is the full source memory-function
  type. The record constructor and three projections below are definitional.

  T and Z are exactly the finite source tree and degenerate zipper datatypes.
  Their tagged constructors are injective and disjoint in SetMM, while
  closure, exhaustiveness, and structural induction exclude missing finite
  values and extraneous non-well-founded values. R, P, I, and Q are the
  complete recursive root, istree, inorder, and zip operations. The unused
  source function inorderz does not occur in this verification condition and
  is omitted.

  G is the arbitrary source predicate eq_loc. Its two call-specific result
  specifications remain implications inside the generated VC; no stronger
  global equality specification is assumed. Proposition-valued conditionals
  are represented by equivalent exhaustive guarded disjunctions.

  NTP4VCTDDistinct is exact finite-list distinctness. The match predicates
  preserve every source Empty/Node case. The remaining predicates only factor
  the original nested weakest-precondition formula: expanding them recovers
  all local lets, universally quantified loop states and updated memories,
  both branches, repeated conjuncts, and the final inorder matches. Every
  internal match witness remains internally existential. The final $a is
  Metamath's native unproved statement encoding; every preceding $a is syntax
  or a faithful definition, and this database contains no $p declaration.
$)

$c
  NTP4VCTDNodeType NTP4VCTDMemoryType
  NTP4VCTDNodeRecord NTP4VCTDLeft NTP4VCTDRight NTP4VCTDData
  NTP4VCTDEmpty NTP4VCTDNode NTP4VCTDTop NTP4VCTDZLeft
  NTP4VCTDDistinct
  NTP4VCTDLeftMatch NTP4VCTDRightMatch NTP4VCTDChildMatch
  NTP4VCTDInitialInorder NTP4VCTDFinalInorder
  NTP4VCTDThen NTP4VCTDInnerTrue NTP4VCTDInnerFalse
  NTP4VCTDInner NTP4VCTDLoop NTP4VCTDOuterElse NTP4VCTDGoal
$.

$v mem1 o3 o4 o6 o7 pl pp ppr subtree zipper1 $.

ntp4vctd-var-mem1 $f class mem1 $.
ntp4vctd-var-o3 $f class o3 $.
ntp4vctd-var-o4 $f class o4 $.
ntp4vctd-var-o6 $f class o6 $.
ntp4vctd-var-o7 $f class o7 $.
ntp4vctd-var-pl $f class pl $.
ntp4vctd-var-pp $f class pp $.
ntp4vctd-var-ppr $f class ppr $.
ntp4vctd-var-subtree $f class subtree $.
ntp4vctd-var-zipper1 $f class zipper1 $.

ntp4vctd-node-type-syntax
  $a class ( NTP4VCTDNodeType A ) $.
ntp4vctd-memory-type-syntax
  $a class ( NTP4VCTDMemoryType A ) $.
ntp4vctd-node-record-syntax
  $a class ( NTP4VCTDNodeRecord A B C ) $.
ntp4vctd-left-syntax
  $a class ( NTP4VCTDLeft A ) $.
ntp4vctd-right-syntax
  $a class ( NTP4VCTDRight A ) $.
ntp4vctd-data-syntax
  $a class ( NTP4VCTDData A ) $.
ntp4vctd-empty-syntax
  $a class NTP4VCTDEmpty $.
ntp4vctd-node-syntax
  $a class ( NTP4VCTDNode A B C ) $.
ntp4vctd-top-syntax
  $a class NTP4VCTDTop $.
ntp4vctd-zleft-syntax
  $a class ( NTP4VCTDZLeft A B C ) $.
ntp4vctd-distinct-syntax
  $a wff ( NTP4VCTDDistinct A B ) $.
ntp4vctd-left-match-syntax
  $a wff ( NTP4VCTDLeftMatch A B C D ) $.
ntp4vctd-right-match-syntax
  $a wff ( NTP4VCTDRightMatch A B C D ) $.
ntp4vctd-child-match-syntax
  $a wff ( NTP4VCTDChildMatch A B C D ) $.
ntp4vctd-initial-inorder-syntax
  $a wff ( NTP4VCTDInitialInorder A B C D E F ) $.
ntp4vctd-final-inorder-syntax
  $a wff ( NTP4VCTDFinalInorder A B C D E F G ) $.
ntp4vctd-then-syntax
  $a wff ( NTP4VCTDThen A B C D E F G H ) $.
ntp4vctd-inner-true-syntax
  $a wff (
    NTP4VCTDInnerTrue A B C D E F G H I J K
  ) $.
ntp4vctd-inner-false-syntax
  $a wff (
    NTP4VCTDInnerFalse A B C D E F G H I J K L M
  ) $.
ntp4vctd-inner-syntax
  $a wff (
    NTP4VCTDInner A B C D E F G H I J K L M N
  ) $.
ntp4vctd-loop-syntax
  $a wff ( NTP4VCTDLoop A B C D E F G H I J K ) $.
ntp4vctd-outer-else-syntax
  $a wff ( NTP4VCTDOuterElse A B C D E F G H I J K ) $.
ntp4vctd-goal-syntax
  $a wff ( NTP4VCTDGoal A B C D E F G H I J K ) $.

ntp4vctd-node-type-definition $a |- (
  NTP4VCTDNodeType A
) = (
  A X. ( A X. ZZ )
) $.

ntp4vctd-memory-type-definition $a |- (
  NTP4VCTDMemoryType A
) = (
  ( NTP4VCTDNodeType A ) ^m A
) $.

ntp4vctd-node-record-definition $a |- (
  NTP4VCTDNodeRecord A B C
) = <. A , <. B , C >. >. $.

ntp4vctd-left-definition $a |- (
  NTP4VCTDLeft A
) = ( 1st ` A ) $.

ntp4vctd-right-definition $a |- (
  NTP4VCTDRight A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vctd-data-definition $a |- (
  NTP4VCTDData A
) = ( 2nd ` ( 2nd ` A ) ) $.

ntp4vctd-empty-definition $a |- (
  NTP4VCTDEmpty
) = <. 0 , (/) >. $.

ntp4vctd-node-definition $a |- (
  NTP4VCTDNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vctd-top-definition $a |- (
  NTP4VCTDTop
) = <. 0 , (/) >. $.

ntp4vctd-zleft-definition $a |- (
  NTP4VCTDZLeft A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

${
  $d i j A B $.

  ntp4vctd-distinct-definition $a |- (
    NTP4VCTDDistinct A B
  ) <-> (
    A e. Word B
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i =/= j
          ->
          ( A ` i ) =/= ( A ` j )
        )
  ) $.
$}

${
  $d p r A B C D $.

  ntp4vctd-left-match-definition $a |- (
    NTP4VCTDLeftMatch A B C D
  ) <-> (
    E. p e. C E. r e. D
      A = ( NTP4VCTDNode B p r )
  ) $.
$}

${
  $d l p A B C D $.

  ntp4vctd-right-match-definition $a |- (
    NTP4VCTDRightMatch A B C D
  ) <-> (
    E. l e. D E. p e. C
      A = ( NTP4VCTDNode l p B )
  ) $.
$}

${
  $d l p r A B C D $.

  ntp4vctd-child-match-definition $a |- (
    NTP4VCTDChildMatch A B C D
  ) <-> (
    E. l e. D E. p e. C E. r e. D
      (
        A = ( NTP4VCTDNode l p r )
        /\
        (
          l = B
          \/
          r = B
        )
      )
  ) $.
$}

${
  $d l p A B C D E F $.

  ntp4vctd-initial-inorder-definition $a |- (
    NTP4VCTDInitialInorder A B C D E F
  ) <-> (
    E. p e. F E. l e. Word F
      (
        ( E ` B ) = ( <" p "> ++ l )
        /\
        (
          (
            NTP4VCTDData
              ( A ` ( D ` B ) )
          ) = (
            NTP4VCTDData
              ( A ` p )
          )
          /\
          ( E ` C ) = l
        )
      )
  ) $.
$}

${
  $d l p A B C D E F G $.

  ntp4vctd-final-inorder-definition $a |- (
    NTP4VCTDFinalInorder A B C D E F G
  ) <-> (
    E. p e. G E. l e. Word G
      (
        ( F ` C ) = ( <" p "> ++ l )
        /\
        (
          (
            NTP4VCTDData
              (
                A `
                (
                  NTP4VCTDLeft
                    ( A ` D )
                )
              )
          ) = (
            NTP4VCTDData
              ( B ` p )
          )
          /\
          ( F ` E ) = l
        )
      )
  ) $.
$}

${
  $d l p r A B C D E F G H $.

  ntp4vctd-then-definition $a |- (
    NTP4VCTDThen A B C D E F G H
  ) <-> (
    (
      ( F ` B ) =/= H
      /\
      ( F ` B ) =/= H
    )
    /\
    E. l e. D E. p e. C E. r e. D
      (
        B = ( NTP4VCTDNode l p r )
        /\
        (
          <. A , r >. e. E
          /\
          (
            ( F ` r )
            =
            (
              NTP4VCTDRight
                ( A ` ( F ` B ) )
            )
            /\
            (
              NTP4VCTDInitialInorder
                A B r F G C
            )
          )
        )
      )
  ) $.
$}

${
  $d o6 o7 A B C D E F G H I J K $.

  ntp4vctd-inner-true-definition $a |- (
    NTP4VCTDInnerTrue A B C D E F G H I J K
  ) <-> (
    B =/= NTP4VCTDEmpty
    /\
    A. o6 e. H
      (
        ( NTP4VCTDRightMatch B o6 G H )
        ->
        (
          B =/= NTP4VCTDEmpty
          /\
          A. o7 e. H
            (
              ( NTP4VCTDLeftMatch B o7 G H )
              ->
              (
                (
                  NTP4VCTDLeft
                    (
                      A `
                      (
                        NTP4VCTDLeft
                          ( A ` E )
                      )
                    )
                ) =/= K
                /\
                (
                  ( NTP4VCTDChildMatch B o7 G H )
                  /\
                  (
                    (
                      NTP4VCTDLeft
                        ( A ` E )
                    ) =/= K
                    /\
                    (
                      (
                        NTP4VCTDLeft
                          (
                            A `
                            (
                              NTP4VCTDLeft
                                ( A ` E )
                            )
                          )
                      ) =/= K
                      /\
                      (
                        <.
                          A ,
                          (
                            NTP4VCTDNode
                              o7
                              (
                                NTP4VCTDLeft
                                  ( A ` E )
                              )
                              o6
                          )
                        >. e. I
                        /\
                        (
                          J `
                          <.
                            (
                              NTP4VCTDNode
                                o7
                                (
                                  NTP4VCTDLeft
                                    ( A ` E )
                                )
                                o6
                            ) ,
                            ( NTP4VCTDZLeft D E C )
                          >.
                        ) = F
                      )
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
  $d mem1 o6 p pl q
     A B C D E F G H I J K L M $.

  ntp4vctd-inner-false-definition $a |- (
    NTP4VCTDInnerFalse A B C D E F G H I J K L M
  ) <-> (
    (
      (
        NTP4VCTDLeft
          ( A ` E )
      ) =/= M
      /\
      (
        NTP4VCTDLeft
          ( A ` E )
      ) =/= M
    )
    /\
    (
      E =/= M
      /\
      A. mem1 e. ( NTP4VCTDMemoryType G )
        (
          (
            (
              mem1 ` E
            ) = (
              NTP4VCTDNodeRecord
                (
                  NTP4VCTDRight
                    (
                      A `
                      (
                        NTP4VCTDLeft
                          ( A ` E )
                      )
                    )
                )
                (
                  NTP4VCTDRight
                    ( A ` E )
                )
                (
                  NTP4VCTDData
                    ( A ` E )
                )
            )
            /\
            A. q e. G
              (
                q =/= E
                ->
                ( mem1 ` q ) = ( A ` q )
              )
          )
          ->
          (
            B =/= NTP4VCTDEmpty
            /\
            A. pl e. H
              (
                ( NTP4VCTDLeftMatch B pl G H )
                ->
                (
                  B =/= NTP4VCTDEmpty
                  /\
                  A. o6 e. H
                    (
                      ( NTP4VCTDRightMatch B o6 G H )
                      ->
                      (
                        A. p e. G
                          (
                            NTP4VCTDData
                              ( mem1 ` p )
                          ) = (
                            NTP4VCTDData
                              ( A ` p )
                          )
                        /\
                        (
                          <.
                            mem1 ,
                            (
                              J `
                              <.
                                o6 ,
                                ( NTP4VCTDZLeft D E C )
                              >.
                            )
                          >. e. I
                          /\
                          (
                            (
                              K `
                              (
                                J `
                                <.
                                  o6 ,
                                  ( NTP4VCTDZLeft D E C )
                                >.
                              )
                            ) = ( K ` F )
                            /\
                            (
                              NTP4VCTDFinalInorder
                                A
                                mem1
                                F
                                E
                                (
                                  J `
                                  <.
                                    o6 ,
                                    ( NTP4VCTDZLeft D E C )
                                  >.
                                )
                                L
                                G
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
  ) $.
$}

${
  $d A B C D E F G H I J K L M N $.

  ntp4vctd-inner-definition $a |- (
    NTP4VCTDInner A B C D E F G H I J K L M N
  ) <-> (
    (
      (
        <.
          (
            NTP4VCTDLeft
              (
                A `
                (
                  NTP4VCTDLeft
                    ( A ` E )
                )
              )
          ) ,
          N
        >. e. M
      )
      <->
      (
        NTP4VCTDLeft
          (
            A `
            (
              NTP4VCTDLeft
                ( A ` E )
            )
          )
      ) = N
    )
    ->
    (
      (
        -.
        <.
          (
            NTP4VCTDLeft
              (
                A `
                (
                  NTP4VCTDLeft
                    ( A ` E )
                )
              )
          ) ,
          N
        >. e. M
        /\
        (
          NTP4VCTDInnerTrue
            A B C D E F G H I J N
        )
      )
      \/
      (
        <.
          (
            NTP4VCTDLeft
              (
                A `
                (
                  NTP4VCTDLeft
                    ( A ` E )
                )
              )
          ) ,
          N
        >. e. M
        /\
        (
          NTP4VCTDInnerFalse
            A B C D E F G H I J K L N
        )
      )
    )
  ) $.
$}

${
  $d pp ppr subtree zipper1
     A B C D E F G H I J K $.

  ntp4vctd-loop-definition $a |- (
    NTP4VCTDLoop A B C D E F G H I J K
  ) <-> (
    A. subtree e. D A. ppr e. D
      A. zipper1 e. E A. pp e. C
        (
          (
            pp =/= K
            /\
            (
              (
                NTP4VCTDLeft
                  ( A ` pp )
              ) =/= K
              /\
              (
                <.
                  A ,
                  ( NTP4VCTDNode subtree pp ppr )
                >. e. F
                /\
                (
                  G `
                  <.
                    ( NTP4VCTDNode subtree pp ppr ) ,
                    zipper1
                  >.
                ) = B
              )
            )
          )
          ->
          (
            NTP4VCTDInner
              A subtree ppr zipper1 pp B C D
              F G H I J K
          )
        )
  ) $.
$}

${
  $d o3 o4 A B C D E F G H I J K $.

  ntp4vctd-outer-else-definition $a |- (
    NTP4VCTDOuterElse A B C D E F G H I J K
  ) <-> (
    (
      NTP4VCTDLeft
        ( A ` ( H ` B ) )
    ) =/= K
    /\
    (
      B =/= NTP4VCTDEmpty
      /\
      A. o3 e. D
        (
          ( NTP4VCTDRightMatch B o3 C D )
          ->
          (
            B =/= NTP4VCTDEmpty
            /\
            A. o4 e. D
              (
                ( NTP4VCTDLeftMatch B o4 C D )
                ->
                (
                  (
                    (
                      ( H ` B ) =/= K
                      /\
                      (
                        NTP4VCTDLeft
                          ( A ` ( H ` B ) )
                      ) = (
                        NTP4VCTDLeft
                          ( A ` ( H ` B ) )
                      )
                    )
                    /\
                    (
                      (
                        NTP4VCTDLeft
                          ( A ` ( H ` B ) )
                      ) =/= K
                      /\
                      (
                        <.
                          A ,
                          (
                            NTP4VCTDNode
                              o4
                              ( H ` B )
                              o3
                          )
                        >. e. F
                        /\
                        (
                          G `
                          <.
                            (
                              NTP4VCTDNode
                                o4
                                ( H ` B )
                                o3
                            ) ,
                            NTP4VCTDTop
                          >.
                        ) = B
                      )
                    )
                  )
                  /\
                  (
                    NTP4VCTDLoop
                      A B C D E F G H I J K
                  )
                )
              )
          )
        )
    )
  ) $.
$}

${
  $d A B C D E F G H I J K $.

  ntp4vctd-goal-definition $a |- (
    NTP4VCTDGoal A B C D E F G H I J K
  ) <-> (
    ( H ` B ) =/= K
    /\
    (
      (
        <.
          (
            NTP4VCTDLeft
              ( A ` ( H ` B ) )
          ) ,
          K
        >. e. J
      )
      <->
      (
        NTP4VCTDLeft
          ( A ` ( H ` B ) )
      ) = K
    )
    ->
    (
      (
        <.
          (
            NTP4VCTDLeft
              ( A ` ( H ` B ) )
          ) ,
          K
        >. e. J
        /\
        (
          NTP4VCTDThen
            A B C D F H I K
        )
      )
      \/
      (
        -.
        <.
          (
            NTP4VCTDLeft
              ( A ` ( H ` B ) )
          ) ,
          K
        >. e. J
        /\
        (
          NTP4VCTDOuterElse
            A B C D E F G H I J K
        )
      )
    )
  ) $.
$}

${
  $d l m p r s t x z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact source type context. $)
  ntp4vctd-location-carrier-nonempty $e |- U =/= (/) $.
  ntp4vctd-null-location $e |- E e. U $.
  ntp4vctd-eq-loc-predicate $e |- G C_ ( U X. U ) $.

  $( Exact finite tree datatype over locations. $)
  ntp4vctd-tree-empty-closure $e |- NTP4VCTDEmpty e. T $.

  ntp4vctd-tree-node-closure $e |- A. l e. T A. p e. U A. r e. T
    ( NTP4VCTDNode l p r ) e. T $.

  ntp4vctd-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCTDEmpty
      \/
      E. l e. T E. p e. U E. r e. T
        t = ( NTP4VCTDNode l p r )
    ) $.

  ntp4vctd-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCTDEmpty e. s
        /\
        A. l e. T A. p e. U A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCTDNode l p r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Exact finite zipper datatype for left descent. $)
  ntp4vctd-zipper-top-closure $e |- NTP4VCTDTop e. Z $.

  ntp4vctd-zipper-left-closure $e |- A. z e. Z A. p e. U A. r e. T
    ( NTP4VCTDZLeft z p r ) e. Z $.

  ntp4vctd-zipper-constructor-exhaustive $e |- A. z e. Z
    (
      z = NTP4VCTDTop
      \/
      E. x e. Z E. p e. U E. r e. T
        z = ( NTP4VCTDZLeft x p r )
    ) $.

  ntp4vctd-zipper-structural-induction $e |- A. s e. ~P Z
    (
      (
        NTP4VCTDTop e. s
        /\
        A. z e. Z A. p e. U A. r e. T
          (
            z e. s
            ->
            ( NTP4VCTDZLeft z p r ) e. s
          )
      )
      ->
      s = Z
    ) $.

  $( Complete source operation types. $)
  ntp4vctd-root-function $e |- R e. ( U ^m T ) $.
  ntp4vctd-istree-relation $e |- P C_
    ( ( NTP4VCTDMemoryType U ) X. T ) $.
  ntp4vctd-inorder-function $e |- I e. ( ( Word U ) ^m T ) $.
  ntp4vctd-zip-function $e |- Q e. ( T ^m ( T X. Z ) ) $.

  $( Complete recursive root equations. $)
  ntp4vctd-root-empty $e |- (
    R ` NTP4VCTDEmpty
  ) = E $.

  ntp4vctd-root-node $e |- A. l e. T A. p e. U A. r e. T
    (
      R ` ( NTP4VCTDNode l p r )
    ) = p $.

  $( Complete recursive istree equations. $)
  ntp4vctd-istree-empty $e |- A. m e. ( NTP4VCTDMemoryType U )
    <. m , NTP4VCTDEmpty >. e. P $.

  ntp4vctd-istree-node $e |- A. m e. ( NTP4VCTDMemoryType U )
    A. l e. T A. p e. U A. r e. T
      (
        <. m , ( NTP4VCTDNode l p r ) >. e. P
        <->
        (
          p =/= E
          /\
          (
            <. m , l >. e. P
            /\
            (
              <. m , r >. e. P
              /\
              (
                ( R ` l )
                =
                (
                  NTP4VCTDLeft
                    ( m ` p )
                )
                /\
                ( R ` r )
                =
                (
                  NTP4VCTDRight
                    ( m ` p )
                )
              )
            )
          )
        )
      ) $.

  $( Complete recursive inorder equations. $)
  ntp4vctd-inorder-empty $e |- (
    I ` NTP4VCTDEmpty
  ) = (/) $.

  ntp4vctd-inorder-node $e |- A. l e. T A. p e. U A. r e. T
    (
      I ` ( NTP4VCTDNode l p r )
    ) = (
      ( I ` l )
      ++
      (
        <" p ">
        ++
        ( I ` r )
      )
    ) $.

  $( Complete recursive zip equations. $)
  ntp4vctd-zip-top $e |- A. t e. T
    (
      Q ` <. t , NTP4VCTDTop >.
    ) = t $.

  ntp4vctd-zip-left $e |- A. t e. T A. z e. Z
    A. p e. U A. r e. T
      (
        Q ` <. t , ( NTP4VCTDZLeft z p r ) >.
      ) = (
        Q ` <. ( NTP4VCTDNode t p r ) , z >.
      ) $.

  $( Source theorem parameters and fact0--fact2. $)
  ntp4vctd-it-tree $e |- A e. T $.
  ntp4vctd-memory $e |- B e. ( NTP4VCTDMemoryType U ) $.
  ntp4vctd-fact0 $e |- ( R ` A ) =/= E $.
  ntp4vctd-fact1 $e |- <. B , A >. e. P $.
  ntp4vctd-fact2 $e |- ( NTP4VCTDDistinct ( I ` A ) U ) $.

  ntp4vctd-pearl-search-tree-delete-min-vc $a |- (
    NTP4VCTDGoal
      B A U T Z P Q R I G E
  ) $.
$}
