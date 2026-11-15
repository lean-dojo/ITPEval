$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_mergeqtvc: the Braun-heap merge verification
  condition establishes its recursive-call obligations and shows that the
  merged tree preserves the heap and Braun size invariants while combining
  the two input trees' occurrence counts. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt and D is its total
  preorder. T is exactly the source inductive binary-tree carrier:
  NTP4VCEmpty and NTP4VCNode give disjoint injective tagged constructors,
  while constructor closure, exhaustiveness, and structural induction rule
  out both missing finite trees and extraneous non-well-founded values.

  L, H, I, O, and S represent le_root, heap, inv, occ, and size. Their
  equations below are the complete source recursive definitions over T and
  the full integer domain ZZ. M represents minimum: its type and Node
  equation retain exactly the source specification, including its arbitrary
  value on Empty.

  NTP4VCMergeEntry and NTP4VCMergeResultAntecedent expand the source tree
  matches into disjoint Empty and Node cases. Each source conditional on le
  is the classically equivalent split into le and not-le branches. All
  recursive-result trees and the removed element remain existentially
  quantified inside their original branches, while the final result tree
  remains universally quantified. The final $a declaration is Metamath's
  native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode
  NTP4VCMergeEntry NTP4VCMergeResultAntecedent
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.

ntp4vc-merge-entry-syntax
  $a wff ( NTP4VCMergeEntry A B C D E F G H I ) $.

ntp4vc-merge-result-antecedent-syntax
  $a wff (
    NTP4VCMergeResultAntecedent A B C D E F G H I J K
  ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

${
  $d e l o q r s t u v x y z
     A B C D E F G H I $.

  $(
    A=l, B=r, C=tree, D=elt, E=le, F=heap, G=inv,
    H=occ, and I=size.
  $)
  ntp4vc-merge-entry-def $a |- (
    ( NTP4VCMergeEntry A B C D E F G H I )
    <->
    (
      B = NTP4VCEmpty
      \/
      E. x e. C E. y e. D E. z e. C
        (
          B = ( NTP4VCNode x y z )
          /\
          E. q e. C E. u e. D E. v e. C
            (
              A = ( NTP4VCNode q u v )
              /\
              (
                (
                  <. u , y >. e. E
                  /\
                  (
                    (
                      0 <_ ( ( I ` A ) + ( I ` B ) )
                      /\
                      (
                        ( ( I ` q ) + ( I ` v ) )
                        <
                        ( ( I ` A ) + ( I ` B ) )
                      )
                    )
                    /\
                    (
                      (
                        q e. F
                        /\
                        v e. F
                      )
                      /\
                      (
                        (
                          q e. G
                          /\
                          v e. G
                        )
                        /\
                        (
                          ( I ` v ) <_ ( I ` q )
                          /\
                          ( I ` q ) <_ ( ( I ` v ) + 1 )
                        )
                      )
                    )
                  )
                )
                \/
                (
                  -. <. u , y >. e. E
                  /\
                  (
                    (
                      A e. F
                      /\
                      (
                        A e. G
                        /\
                        0 < ( I ` A )
                      )
                    )
                    /\
                    A. e e. D A. t e. C
                      (
                        (
                          t e. F
                          /\
                          (
                            t e. G
                            /\
                            (
                              ( I ` t ) = ( ( I ` A ) - 1 )
                              /\
                              (
                                (
                                  H ` <. e , t >.
                                )
                                =
                                (
                                  ( H ` <. e , A >. )
                                  -
                                  1
                                )
                                /\
                                A. s e. D
                                  (
                                    s =/= e
                                    ->
                                    (
                                      H ` <. s , t >.
                                    )
                                    =
                                    (
                                      H ` <. s , A >.
                                    )
                                  )
                              )
                            )
                          )
                        )
                        ->
                        (
                          B e. F
                          /\
                          (
                            B e. G
                            /\
                            0 < ( I ` B )
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
  $d e l o q r s t u v x y z
     A B C D E F G H I J K $.

  $(
    A=result, B=l, C=r, D=tree, E=elt, F=le, G=heap, H=inv,
    I=occ, J=size, and K=minimum.
  $)
  ntp4vc-merge-result-antecedent-def $a |- (
    (
      NTP4VCMergeResultAntecedent
        A B C D E F G H I J K
    )
    <->
    (
      (
        C = NTP4VCEmpty
        /\
        A = B
      )
      \/
      E. x e. D E. y e. E E. z e. D
        (
          C = ( NTP4VCNode x y z )
          /\
          E. q e. D E. u e. E E. v e. D
            (
              B = ( NTP4VCNode q u v )
              /\
              (
                (
                  <. u , y >. e. F
                  /\
                  E. o e. D
                    (
                      (
                        o e. G
                        /\
                        (
                          o e. H
                          /\
                          (
                            A. e e. E
                              (
                                I ` <. e , o >.
                              )
                              =
                              (
                                ( I ` <. e , q >. )
                                +
                                ( I ` <. e , v >. )
                              )
                            /\
                            (
                              J ` o
                            )
                            =
                            (
                              ( J ` q )
                              +
                              ( J ` v )
                            )
                          )
                        )
                      )
                      /\
                      A = ( NTP4VCNode C u o )
                    )
                )
                \/
                (
                  -. <. u , y >. e. F
                  /\
                  E. e e. E E. t e. D
                    (
                      (
                        t e. G
                        /\
                        (
                          t e. H
                          /\
                          (
                            ( J ` t ) = ( ( J ` B ) - 1 )
                            /\
                            (
                              (
                                I ` <. e , t >.
                              )
                              =
                              (
                                ( I ` <. e , B >. )
                                -
                                1
                              )
                              /\
                              A. s e. E
                                (
                                  s =/= e
                                  ->
                                  (
                                    I ` <. s , t >.
                                  )
                                  =
                                  (
                                    I ` <. s , B >.
                                  )
                                )
                            )
                          )
                        )
                      )
                      /\
                      E. o e. D
                        (
                          (
                            o e. G
                            /\
                            (
                              o e. H
                              /\
                              (
                                (
                                  (
                                    e = ( K ` C )
                                    /\
                                    (
                                      I ` <. e , o >.
                                    )
                                    =
                                    (
                                      I ` <. e , C >.
                                    )
                                  )
                                  \/
                                  (
                                    e =/= ( K ` C )
                                    /\
                                    (
                                      (
                                        I ` <. e , o >.
                                      )
                                      =
                                      (
                                        (
                                          I ` <. e , C >.
                                        )
                                        +
                                        1
                                      )
                                      /\
                                      (
                                        I ` <. ( K ` C ) , o >.
                                      )
                                      =
                                      (
                                        (
                                          I ` <. ( K ` C ) , C >.
                                        )
                                        -
                                        1
                                      )
                                    )
                                  )
                                )
                                /\
                                (
                                  A. s e. E
                                    (
                                      s =/= e
                                      ->
                                      (
                                        s =/= ( K ` C )
                                        ->
                                        (
                                          I ` <. s , o >.
                                        )
                                        =
                                        (
                                          I ` <. s , C >.
                                        )
                                      )
                                    )
                                  /\
                                  ( J ` o ) = ( J ` C )
                                )
                              )
                            )
                          )
                          /\
                          A = ( NTP4VCNode o y t )
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
  $d e l o q r s t u v x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carrier elt and its total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-le-relation $e |- D C_ ( U X. U ) $.

  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. D $.

  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. D
        /\
        <. y , z >. e. D
      )
      ->
      <. x , z >. e. D
    ) $.

  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. D
      \/
      <. y , x >. e. D
    ) $.

  $( Exact finite inductive binary-tree carrier over U. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. y e. U A. r e. T
    ( NTP4VCNode l y r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. y e. U E. r e. T
        t = ( NTP4VCNode l y r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. y e. U A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l y r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Types of the source operations used by the VC. $)
  ntp4vc-le-root-relation $e |- L C_ ( U X. T ) $.
  ntp4vc-heap-predicate $e |- H C_ T $.
  ntp4vc-inv-predicate $e |- I C_ T $.
  ntp4vc-occ-function $e |- O e. ( ZZ ^m ( U X. T ) ) $.
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.
  ntp4vc-minimum-function $e |- M e. ( U ^m T ) $.

  $( le_root equations. $)
  ntp4vc-le-root-empty $e |- A. x e. U
    <. x , NTP4VCEmpty >. e. L $.

  ntp4vc-le-root-node $e |- A. x e. U A. l e. T
    A. y e. U A. r e. T
      (
        <. x , ( NTP4VCNode l y r ) >. e. L
        <->
        <. x , y >. e. D
      ) $.

  $( heap equations. $)
  ntp4vc-heap-empty $e |- NTP4VCEmpty e. H $.

  ntp4vc-heap-node $e |- A. l e. T A. y e. U A. r e. T
    (
      ( NTP4VCNode l y r ) e. H
      <->
      (
        <. y , l >. e. L
        /\
        (
          l e. H
          /\
          (
            <. y , r >. e. L
            /\
            r e. H
          )
        )
      )
    ) $.

  $( Braun invariant equations. $)
  ntp4vc-inv-empty $e |- NTP4VCEmpty e. I $.

  ntp4vc-inv-node $e |- A. l e. T A. y e. U A. r e. T
    (
      ( NTP4VCNode l y r ) e. I
      <->
      (
        (
          ( S ` l ) = ( S ` r )
          \/
          ( S ` l ) = ( ( S ` r ) + 1 )
        )
        /\
        (
          l e. I
          /\
          r e. I
        )
      )
    ) $.

  $( Integer-valued occurrence-count equations. $)
  ntp4vc-occ-empty $e |- A. x e. U
    ( O ` <. x , NTP4VCEmpty >. ) = 0 $.

  ntp4vc-occ-node $e |- A. x e. U A. l e. T
    A. y e. U A. r e. T
      (
        O ` <. x , ( NTP4VCNode l y r ) >.
      )
      =
      (
        (
          if ( x = y , 1 , 0 )
          +
          ( O ` <. x , l >. )
        )
        +
        ( O ` <. x , r >. )
      ) $.

  $( Integer-valued size equations. $)
  ntp4vc-size-empty $e |- ( S ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. y e. U A. r e. T
    (
      S ` ( NTP4VCNode l y r )
    )
    =
    (
      ( 1 + ( S ` l ) )
      +
      ( S ` r )
    ) $.

  $( The source minimum specification on nonempty trees. $)
  ntp4vc-minimum-node $e |- A. l e. T A. y e. U A. r e. T
    ( M ` ( NTP4VCNode l y r ) ) = y $.

  $(
    Source theorem parameters A=l and B=r, followed by fact0--fact5.
  $)
  ntp4vc-l-tree $e |- A e. T $.
  ntp4vc-r-tree $e |- B e. T $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- B e. H $.
  ntp4vc-fact2 $e |- A e. I $.
  ntp4vc-fact3 $e |- B e. I $.
  ntp4vc-fact4 $e |- ( S ` B ) <_ ( S ` A ) $.
  ntp4vc-fact5 $e |- ( S ` A ) <_ ( ( S ` B ) + 1 ) $.

  ntp4vc-pearl-braun-trees-braun-heaps-merge-vc $a |- (
    ( NTP4VCMergeEntry A B T U D H I O S )
    /\
    A. q e. T
      (
        (
          NTP4VCMergeResultAntecedent
            q A B T U D H I O S M
        )
        ->
        (
          q e. H
          /\
          (
            q e. I
            /\
            (
              A. e e. U
                (
                  O ` <. e , q >.
                )
                =
                (
                  ( O ` <. e , A >. )
                  +
                  ( O ` <. e , B >. )
                )
              /\
              ( S ` q ) = ( ( S ` A ) + ( S ` B ) )
            )
          )
        )
      )
  ) $.
$}
