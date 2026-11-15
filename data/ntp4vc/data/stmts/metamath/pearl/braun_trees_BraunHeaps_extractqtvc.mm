$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_extractqtvc: the Braun-heap extraction
  verification condition establishes the recursive extraction obligation and
  preserves the heap and Braun size invariants while removing one occurrence
  of the extracted element. This file contains no proof.
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
  the full integer domain ZZ. Consequently these externally named operations
  are uniquely determined by structural recursion and add no mathematical
  premise beyond the source definitions.

  Each source tree match is expanded into its disjoint Empty,
  Node Empty, and Node-with-nonempty-left-subtree cases. The recursive
  extraction witness remains existentially quantified inside that final
  branch, while the extracted element and result tree retain their source
  universal scopes. The final assertion preserves both source conclusions:
  the recursive-call obligation and the heap, invariant, size, and occurrence
  postconditions. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c NTP4VCEmpty NTP4VCNode $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

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

  $(
    Exact finite inductive binary-tree carrier over U.
  $)
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

  $( Types of the five source recursive definitions used by the VC. $)
  ntp4vc-le-root-relation $e |- L C_ ( U X. T ) $.
  ntp4vc-heap-predicate $e |- H C_ T $.
  ntp4vc-inv-predicate $e |- I C_ T $.
  ntp4vc-occ-function $e |- O e. ( ZZ ^m ( U X. T ) ) $.
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.

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

  $( Source theorem parameter A=t, followed by fact0--fact2. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- A e. I $.
  ntp4vc-fact2 $e |- 0 < ( S ` A ) $.

  ntp4vc-pearl-braun-trees-braun-heaps-extract-vc $a |- (
    (
      E. y e. U E. r e. T
        A = ( NTP4VCNode NTP4VCEmpty y r )
      \/
      E. l e. T E. y e. U E. r e. T
        (
          l =/= NTP4VCEmpty
          /\
          (
            A = ( NTP4VCNode l y r )
            /\
            (
              (
                (
                  l = l
                  \/
                  r = l
                )
                /\
                l e. H
              )
              /\
              (
                l e. I
                /\
                0 < ( S ` l )
              )
            )
          )
        )
    )
    /\
    A. e e. U A. q e. T
      (
        (
          E. y e. U E. r e. T
            (
              A = ( NTP4VCNode NTP4VCEmpty y r )
              /\
              (
                e = y
                /\
                q = NTP4VCEmpty
              )
            )
          \/
          E. l e. T E. y e. U E. r e. T
            (
              l =/= NTP4VCEmpty
              /\
              (
                A = ( NTP4VCNode l y r )
                /\
                E. o e. T
                  (
                    (
                      (
                        o e. H
                        /\
                        o e. I
                      )
                      /\
                      (
                        ( S ` o ) = ( ( S ` l ) - 1 )
                        /\
                        (
                          ( O ` <. e , o >. )
                          =
                          ( ( O ` <. e , l >. ) - 1 )
                          /\
                          A. x e. U
                            (
                              x =/= e
                              ->
                              ( O ` <. x , o >. )
                              =
                              ( O ` <. x , l >. )
                            )
                        )
                      )
                    )
                    /\
                    q = ( NTP4VCNode r y o )
                  )
              )
            )
        )
        ->
        (
          q e. H
          /\
          (
            q e. I
            /\
            (
              ( S ` q ) = ( ( S ` A ) - 1 )
              /\
              (
                ( O ` <. e , q >. )
                =
                ( ( O ` <. e , A >. ) - 1 )
                /\
                A. x e. U
                  (
                    x =/= e
                    ->
                    ( O ` <. x , q >. )
                    =
                    ( O ` <. x , A >. )
                  )
              )
            )
          )
        )
      )
  ) $.
$}
