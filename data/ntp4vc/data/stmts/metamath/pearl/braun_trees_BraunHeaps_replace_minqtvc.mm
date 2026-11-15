$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_replace_minqtvc: the Braun-heap replace-minimum
  verification condition establishes the recursive replacement obligations
  and preserves the heap and Braun size invariants while updating exactly the
  required occurrence counts. This file contains no proof.
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

  NTP4VCReplacePost is the source recursive replacement postcondition.
  NTP4VCReplaceEntry and NTP4VCReplaceResultAntecedent expand the source tree
  matches into their disjoint Node and Empty cases; the omitted Empty branch
  is False. Source Booleans use SetMM's exact two-element carrier 2, with
  true=1 and false=0. Proposition-valued conditionals are rendered as
  exhaustive guarded disjunctions. The Boolean, recursive-result, element,
  and final-result quantifiers retain their original scopes and full domains.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode
  NTP4VCReplacePost NTP4VCReplaceEntry
  NTP4VCReplaceResultAntecedent
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.

ntp4vc-replace-post-syntax
  $a wff ( NTP4VCReplacePost A B C D E F G H I ) $.

ntp4vc-replace-entry-syntax
  $a wff ( NTP4VCReplaceEntry A B C D E F G H I J ) $.

ntp4vc-replace-result-antecedent-syntax
  $a wff (
    NTP4VCReplaceResultAntecedent A B C D E F G H I J K
  ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

${
  $d e l o q r s t u v x y z
     A B C D E F G H I $.

  $(
    A=o2, B=x, C=subtree, D=elt, E=heap, F=inv,
    G=occ, H=size, and I=minimum.
  $)
  ntp4vc-replace-post-def $a |- (
    ( NTP4VCReplacePost A B C D E F G H I )
    <->
    (
      A e. E
      /\
      (
        A e. F
        /\
        (
          (
            (
              B = ( I ` C )
              /\
              (
                G ` <. B , A >.
              )
              =
              (
                G ` <. B , C >.
              )
            )
            \/
            (
              B =/= ( I ` C )
              /\
              (
                (
                  G ` <. B , A >.
                )
                =
                (
                  ( G ` <. B , C >. )
                  +
                  1
                )
                /\
                (
                  G ` <. ( I ` C ) , A >.
                )
                =
                (
                  ( G ` <. ( I ` C ) , C >. )
                  -
                  1
                )
              )
            )
          )
          /\
          (
            A. e e. D
              (
                e =/= B
                ->
                (
                  e =/= ( I ` C )
                  ->
                  (
                    G ` <. e , A >.
                  )
                  =
                  (
                    G ` <. e , C >.
                  )
                )
              )
            /\
            ( H ` A ) = ( H ` C )
          )
        )
      )
    )
  ) $.
$}

${
  $d b e l o q r s t u v x y z
     A B C D E F G H I J $.

  $(
    A=t, B=x, C=tree, D=elt, E=le_root, F=heap, G=inv,
    H=occ, I=size, and J=minimum.
  $)
  ntp4vc-replace-entry-def $a |- (
    ( NTP4VCReplaceEntry A B C D E F G H I J )
    <->
    E. l e. C E. y e. D E. r e. C
      (
        A = ( NTP4VCNode l y r )
        /\
        A. b e. { 0 , 1 }
          (
            b = if (
              <. B , l >. e. E ,
              if ( <. B , r >. e. E , 1 , 0 ) ,
              0
            )
            ->
            (
              b =/= 1
              ->
              (
                (
                  l e. F
                  /\
                  0 < ( I ` l )
                )
                /\
                (
                  (
                    <. ( J ` l ) , r >. e. E
                    /\
                    (
                      (
                        l = l
                        \/
                        r = l
                      )
                      /\
                      (
                        l e. F
                        /\
                        (
                          l e. G
                          /\
                          0 < ( I ` l )
                        )
                      )
                    )
                  )
                  \/
                  (
                    -. <. ( J ` l ) , r >. e. E
                    /\
                    (
                      (
                        (
                          l = r
                          \/
                          r = r
                        )
                        /\
                        (
                          r e. F
                          /\
                          (
                            r e. G
                            /\
                            0 < ( I ` r )
                          )
                        )
                      )
                      /\
                      A. o e. C
                        (
                          (
                            NTP4VCReplacePost
                              o B r D F G H I J
                          )
                          ->
                          (
                            r e. F
                            /\
                            0 < ( I ` r )
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
  $d b e l o q r s t u v x y z
     A B C D E F G H I J K $.

  $(
    A=result, B=t, C=x, D=tree, E=elt, F=le_root,
    G=heap, H=inv, I=occ, J=size, and K=minimum.
  $)
  ntp4vc-replace-result-antecedent-def $a |- (
    (
      NTP4VCReplaceResultAntecedent
        A B C D E F G H I J K
    )
    <->
    E. l e. D E. y e. E E. r e. D
      (
        B = ( NTP4VCNode l y r )
        /\
        E. b e. { 0 , 1 }
          (
            b = if (
              <. C , l >. e. F ,
              if ( <. C , r >. e. F , 1 , 0 ) ,
              0
            )
            /\
            (
              (
                b = 1
                /\
                A = ( NTP4VCNode l C r )
              )
              \/
              (
                b =/= 1
                /\
                (
                  (
                    <. ( K ` l ) , r >. e. F
                    /\
                    E. o e. D
                      (
                        (
                          NTP4VCReplacePost
                            o C l E G H I J K
                        )
                        /\
                        A = (
                          NTP4VCNode o ( K ` l ) r
                        )
                      )
                  )
                  \/
                  (
                    -. <. ( K ` l ) , r >. e. F
                    /\
                    E. o e. D
                      (
                        (
                          NTP4VCReplacePost
                            o C r E G H I J K
                        )
                        /\
                        A = (
                          NTP4VCNode l ( K ` r ) o
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
  $d b e l o q r s t u v x y z
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

  $( Source theorem parameters A=t and X=x, followed by fact0--fact2. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-x-element $e |- X e. U $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- A e. I $.
  ntp4vc-fact2 $e |- 0 < ( S ` A ) $.

  ntp4vc-pearl-braun-trees-braun-heaps-replace-min-vc $a |- (
    (
      NTP4VCReplaceEntry A X T U L H I O S M
    )
    /\
    A. q e. T
      (
        (
          NTP4VCReplaceResultAntecedent
            q A X T U L H I O S M
        )
        ->
        (
          NTP4VCReplacePost
            q X A U H I O S M
        )
      )
  ) $.
$}
