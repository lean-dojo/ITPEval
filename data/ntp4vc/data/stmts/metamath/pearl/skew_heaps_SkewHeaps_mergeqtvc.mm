$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/skew_heaps_SkewHeaps_mergeqtvc: the skew-heap merge verification
  condition establishes the recursive-call obligations and states that merge
  preserves the heap invariant while adding the input trees' sizes and
  occurrence counts. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt and R is its total
  preorder. T is exactly the source inductive binary-tree carrier:
  NTP4VCEmpty and NTP4VCNode are disjoint injective tagged constructors,
  while constructor closure, exhaustiveness, and structural induction exclude
  missing finite trees, extraneous values, and non-well-founded trees.

  L, H, O, and S represent le_root, heap, occ, and size. Their base and
  constructor equations are the complete source recursive definitions over
  T, U, and the full integer domain ZZ.

  NTP4VCMergeEntry and NTP4VCMergeResultAntecedent expand the source nested
  tree matches into exhaustive Empty and Node cases. Each source conditional
  on le is represented by its classically equivalent disjoint le and not-le
  branches. Every recursive-result tree remains existentially quantified
  inside its original branch, while the final result tree remains universally
  quantified. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode
  NTP4VCMergeEntry NTP4VCMergeResultAntecedent
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.

ntp4vc-merge-entry-syntax
  $a wff ( NTP4VCMergeEntry A B C D E F G H ) $.

ntp4vc-merge-result-antecedent-syntax
  $a wff (
    NTP4VCMergeResultAntecedent A B C D E F G H I
  ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C ) =
  <. 1 , <. A , <. B , C >. >. >. $.

${
  $d e l o q r s t u v x y z
     A B C D E F G H $.

  $(
    A=t1, B=t2, C=tree, D=elt, E=le, F=heap, G=occ, and H=size.
  $)
  ntp4vc-merge-entry-def $a |- (
    ( NTP4VCMergeEntry A B C D E F G H )
    <->
    (
      B = NTP4VCEmpty
      \/
      E. l e. C E. x e. D E. r e. C
        (
          B = ( NTP4VCNode l x r )
          /\
          (
            A = NTP4VCEmpty
            \/
            E. u e. C E. y e. D E. v e. C
              (
                A = ( NTP4VCNode u y v )
                /\
                (
                  (
                    <. y , x >. e. E
                    /\
                    (
                      (
                        0 <_ ( ( H ` A ) + ( H ` B ) )
                        /\
                        (
                          ( ( H ` v ) + ( H ` B ) )
                          <
                          ( ( H ` A ) + ( H ` B ) )
                        )
                      )
                      /\
                      (
                        v e. F
                        /\
                        B e. F
                      )
                    )
                  )
                  \/
                  (
                    -. <. y , x >. e. E
                    /\
                    (
                      (
                        0 <_ ( ( H ` A ) + ( H ` B ) )
                        /\
                        (
                          ( ( H ` r ) + ( H ` A ) )
                          <
                          ( ( H ` A ) + ( H ` B ) )
                        )
                      )
                      /\
                      (
                        r e. F
                        /\
                        A e. F
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
     A B C D E F G H I $.

  $(
    A=result, B=t1, C=t2, D=tree, E=elt, F=le, G=heap,
    H=occ, and I=size.
  $)
  ntp4vc-merge-result-antecedent-def $a |- (
    (
      NTP4VCMergeResultAntecedent A B C D E F G H I
    )
    <->
    (
      (
        C = NTP4VCEmpty
        /\
        A = B
      )
      \/
      E. l e. D E. x e. E E. r e. D
        (
          C = ( NTP4VCNode l x r )
          /\
          (
            (
              B = NTP4VCEmpty
              /\
              A = C
            )
            \/
            E. u e. D E. y e. E E. v e. D
              (
                B = ( NTP4VCNode u y v )
                /\
                (
                  (
                    <. y , x >. e. F
                    /\
                    E. o e. D
                      (
                        (
                          o e. G
                          /\
                          (
                            A. e e. E
                              (
                                H ` <. e , o >.
                              )
                              =
                              (
                                ( H ` <. e , v >. )
                                +
                                ( H ` <. e , C >. )
                              )
                            /\
                            ( I ` o ) =
                              ( ( I ` v ) + ( I ` C ) )
                          )
                        )
                        /\
                        A = ( NTP4VCNode o y u )
                      )
                  )
                  \/
                  (
                    -. <. y , x >. e. F
                    /\
                    E. o e. D
                      (
                        (
                          o e. G
                          /\
                          (
                            A. e e. E
                              (
                                H ` <. e , o >.
                              )
                              =
                              (
                                ( H ` <. e , r >. )
                                +
                                ( H ` <. e , B >. )
                              )
                            /\
                            ( I ` o ) =
                              ( ( I ` r ) + ( I ` B ) )
                          )
                        )
                        /\
                        A = ( NTP4VCNode o x l )
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
  ntp4vc-le-relation $e |- R C_ ( U X. U ) $.

  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. R $.

  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.

  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      <. y , x >. e. R
    ) $.

  $( Exact finite inductive binary-tree carrier over U. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. x e. U A. r e. T
    ( NTP4VCNode l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. x e. U E. r e. T
        t = ( NTP4VCNode l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. q e. ~P T
    (
      (
        NTP4VCEmpty e. q
        /\
        A. l e. T A. x e. U A. r e. T
          (
            (
              l e. q
              /\
              r e. q
            )
            ->
            ( NTP4VCNode l x r ) e. q
          )
      )
      ->
      q = T
    ) $.

  $( Types of the source operations used by the verification condition. $)
  ntp4vc-le-root-relation $e |- L C_ ( U X. T ) $.
  ntp4vc-heap-predicate $e |- H C_ T $.
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
        <. x , y >. e. R
      ) $.

  $( heap equations. $)
  ntp4vc-heap-empty $e |- NTP4VCEmpty e. H $.

  ntp4vc-heap-node $e |- A. l e. T A. x e. U A. r e. T
    (
      ( NTP4VCNode l x r ) e. H
      <->
      (
        <. x , l >. e. L
        /\
        (
          l e. H
          /\
          (
            <. x , r >. e. L
            /\
            r e. H
          )
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

  ntp4vc-size-node $e |- A. l e. T A. x e. U A. r e. T
    (
      S ` ( NTP4VCNode l x r )
    )
    =
    (
      ( 1 + ( S ` l ) )
      +
      ( S ` r )
    ) $.

  $( Source theorem parameters A=t1 and B=t2, followed by fact0 and fact1. $)
  ntp4vc-t1-tree $e |- A e. T $.
  ntp4vc-t2-tree $e |- B e. T $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- B e. H $.

  ntp4vc-pearl-skew-heaps-merge-vc $a |- (
    ( NTP4VCMergeEntry A B T U R H O S )
    /\
    A. q e. T
      (
        (
          NTP4VCMergeResultAntecedent
            q A B T U R H O S
        )
        ->
        (
          q e. H
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
  ) $.
$}
