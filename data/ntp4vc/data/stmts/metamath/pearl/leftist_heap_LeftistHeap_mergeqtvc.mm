$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_mergeqtvc: the leftist-heap merge
  verification condition establishes the recursive-call obligations and
  states that a merge preserves the leftist-heap invariant while adding the
  input trees' sizes and occurrence counts. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt and D is its total
  preorder. T is exactly the source inductive carrier of finite rank-labelled
  binary trees. NTP4VCEmpty and NTP4VCNode are disjoint injective tagged
  constructors; closure, exhaustiveness, and structural induction exclude
  missing finite trees, extraneous values, and non-well-founded trees.

  L, H, O, S, K, I, and M represent le_root, is_heap, occ, size, rank,
  leftist, and minimum. Their base and constructor equations are the complete
  source recursive definitions over T, U, and the full integer domain ZZ.
  The minimum equation is the source specification on every nonempty tree.
  NTP4VCMin and NTP4VCLeftistHeap faithfully expand integer minimum and the
  conjunction is_heap /\ leftist.

  NTP4VCMergeEntry and NTP4VCMergeResultAntecedent expand the two source
  nested tree matches into exhaustive Empty and Node cases. Each source
  conditional on le is represented by its classically equivalent disjoint
  le and not-le branches. Every recursive-result tree remains existentially
  quantified inside its original branch, while the final result tree remains
  universally quantified. The final $a declaration is Metamath's native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode NTP4VCMin NTP4VCLeftistHeap
  NTP4VCMergeEntry NTP4VCMergeResultAntecedent
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C D ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-leftist-heap-syntax
  $a wff ( NTP4VCLeftistHeap A B C ) $.
ntp4vc-merge-entry-syntax
  $a wff ( NTP4VCMergeEntry A B C D E F G H I J ) $.
ntp4vc-merge-result-antecedent-syntax
  $a wff (
    NTP4VCMergeResultAntecedent A B C D E F G H I J K
  ) $.

ntp4vc-empty-def $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-def $a |- ( NTP4VCNode A B C D ) =
  <. 1 , <. A , <. B , <. C , D >. >. >. >. $.

ntp4vc-min-def $a |- ( NTP4VCMin A B ) =
  if ( A <_ B , A , B ) $.

ntp4vc-leftist-heap-def $a |- (
  ( NTP4VCLeftistHeap A B C )
  <->
  (
    A e. B
    /\
    A e. C
  )
) $.

${
  $d l o q r s u v x y z
     A B C D E F G H I J $.

  $(
    A=h1, B=h2, C=tree, D=elt, E=le, F=le_root, G=is_heap,
    H=occ, I=size, and J=leftist.
  $)
  ntp4vc-merge-entry-def $a |- (
    ( NTP4VCMergeEntry A B C D E F G H I J )
    <->
    (
      B = NTP4VCEmpty
      \/
      E. s e. ZZ E. l e. C E. x e. D E. r e. C
        (
          B = ( NTP4VCNode s l x r )
          /\
          (
            A = NTP4VCEmpty
            \/
            E. u e. ZZ E. v e. C E. y e. D E. z e. C
              (
                A = ( NTP4VCNode u v y z )
                /\
                (
                  (
                    <. y , x >. e. E
                    /\
                    (
                      (
                        (
                          0 <_ ( ( I ` A ) + ( I ` B ) )
                          /\
                          (
                            ( ( I ` z ) + ( I ` B ) )
                            <
                            ( ( I ` A ) + ( I ` B ) )
                          )
                        )
                        /\
                        (
                          ( NTP4VCLeftistHeap z G J )
                          /\
                          ( NTP4VCLeftistHeap B G J )
                        )
                      )
                      /\
                      A. o e. C
                        (
                          (
                            ( I ` o ) =
                              ( ( I ` z ) + ( I ` B ) )
                            /\
                            (
                              A. q e. D
                                (
                                  H ` <. q , o >.
                                )
                                =
                                (
                                  ( H ` <. q , z >. )
                                  +
                                  ( H ` <. q , B >. )
                                )
                              /\
                              ( NTP4VCLeftistHeap o G J )
                            )
                          )
                          ->
                          (
                            (
                              ( NTP4VCLeftistHeap o G J )
                              /\
                              ( NTP4VCLeftistHeap v G J )
                            )
                            /\
                            (
                              <. y , v >. e. F
                              /\
                              <. y , o >. e. F
                            )
                          )
                        )
                    )
                  )
                  \/
                  (
                    -. <. y , x >. e. E
                    /\
                    (
                      (
                        (
                          0 <_ ( ( I ` A ) + ( I ` B ) )
                          /\
                          (
                            ( ( I ` A ) + ( I ` r ) )
                            <
                            ( ( I ` A ) + ( I ` B ) )
                          )
                        )
                        /\
                        (
                          ( NTP4VCLeftistHeap A G J )
                          /\
                          ( NTP4VCLeftistHeap r G J )
                        )
                      )
                      /\
                      A. o e. C
                        (
                          (
                            ( I ` o ) =
                              ( ( I ` A ) + ( I ` r ) )
                            /\
                            (
                              A. q e. D
                                (
                                  H ` <. q , o >.
                                )
                                =
                                (
                                  ( H ` <. q , A >. )
                                  +
                                  ( H ` <. q , r >. )
                                )
                              /\
                              ( NTP4VCLeftistHeap o G J )
                            )
                          )
                          ->
                          (
                            (
                              ( NTP4VCLeftistHeap o G J )
                              /\
                              ( NTP4VCLeftistHeap l G J )
                            )
                            /\
                            (
                              <. x , l >. e. F
                              /\
                              <. x , o >. e. F
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
  $d l o q r s u v x y z
     A B C D E F G H I J K $.

  $(
    A=result, B=h1, C=h2, D=tree, E=elt, F=le, G=is_heap,
    H=occ, I=size, J=leftist, and K=minimum.
  $)
  ntp4vc-merge-result-antecedent-def $a |- (
    (
      NTP4VCMergeResultAntecedent A B C D E F G H I J K
    )
    <->
    (
      (
        C = NTP4VCEmpty
        /\
        A = B
      )
      \/
      E. s e. ZZ E. l e. D E. x e. E E. r e. D
        (
          C = ( NTP4VCNode s l x r )
          /\
          (
            (
              B = NTP4VCEmpty
              /\
              A = C
            )
            \/
            E. u e. ZZ E. v e. D E. y e. E E. z e. D
              (
                B = ( NTP4VCNode u v y z )
                /\
                (
                  (
                    <. y , x >. e. F
                    /\
                    E. o e. D
                      (
                        (
                          ( I ` o ) =
                            ( ( I ` z ) + ( I ` C ) )
                          /\
                          (
                            A. q e. E
                              (
                                H ` <. q , o >.
                              )
                              =
                              (
                                ( H ` <. q , z >. )
                                +
                                ( H ` <. q , C >. )
                              )
                            /\
                            ( NTP4VCLeftistHeap o G J )
                          )
                        )
                        /\
                        (
                          ( NTP4VCLeftistHeap A G J )
                          /\
                          (
                            ( K ` A ) = y
                            /\
                            (
                              ( I ` A ) =
                                ( ( 1 + ( I ` v ) ) + ( I ` o ) )
                              /\
                              (
                                (
                                  H ` <. y , A >.
                                )
                                =
                                (
                                  ( 1 + ( H ` <. y , v >. ) )
                                  +
                                  ( H ` <. y , o >. )
                                )
                                /\
                                A. q e. E
                                  (
                                    q =/= y
                                    ->
                                    (
                                      H ` <. q , A >.
                                    )
                                    =
                                    (
                                      ( H ` <. q , v >. )
                                      +
                                      ( H ` <. q , o >. )
                                    )
                                  )
                              )
                            )
                          )
                        )
                      )
                  )
                  \/
                  (
                    -. <. y , x >. e. F
                    /\
                    E. o e. D
                      (
                        (
                          ( I ` o ) =
                            ( ( I ` B ) + ( I ` r ) )
                          /\
                          (
                            A. q e. E
                              (
                                H ` <. q , o >.
                              )
                              =
                              (
                                ( H ` <. q , B >. )
                                +
                                ( H ` <. q , r >. )
                              )
                            /\
                            ( NTP4VCLeftistHeap o G J )
                          )
                        )
                        /\
                        (
                          ( NTP4VCLeftistHeap A G J )
                          /\
                          (
                            ( K ` A ) = x
                            /\
                            (
                              ( I ` A ) =
                                ( ( 1 + ( I ` l ) ) + ( I ` o ) )
                              /\
                              (
                                (
                                  H ` <. x , A >.
                                )
                                =
                                (
                                  ( 1 + ( H ` <. x , l >. ) )
                                  +
                                  ( H ` <. x , o >. )
                                )
                                /\
                                A. q e. E
                                  (
                                    q =/= x
                                    ->
                                    (
                                      H ` <. q , A >.
                                    )
                                    =
                                    (
                                      ( H ` <. q , l >. )
                                      +
                                      ( H ` <. q , o >. )
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

  $( Exact finite inductive rank-labelled binary-tree carrier over U. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      ( NTP4VCNode s l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. s e. ZZ E. l e. T E. x e. U E. r e. T
        t = ( NTP4VCNode s l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. q e. ~P T
    (
      (
        NTP4VCEmpty e. q
        /\
        A. s e. ZZ A. l e. T A. x e. U A. r e. T
          (
            (
              l e. q
              /\
              r e. q
            )
            ->
            ( NTP4VCNode s l x r ) e. q
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
  ntp4vc-rank-function $e |- K e. ( ZZ ^m T ) $.
  ntp4vc-leftist-predicate $e |- I C_ T $.
  ntp4vc-minimum-function $e |- M e. ( U ^m T ) $.

  $( le_root equations. $)
  ntp4vc-le-root-empty $e |- A. x e. U
    <. x , NTP4VCEmpty >. e. L $.

  ntp4vc-le-root-node $e |- A. x e. U A. s e. ZZ
    A. l e. T A. y e. U A. r e. T
      (
        <. x , ( NTP4VCNode s l y r ) >. e. L
        <->
        <. x , y >. e. D
      ) $.

  $( is_heap equations. $)
  ntp4vc-heap-empty $e |- NTP4VCEmpty e. H $.

  ntp4vc-heap-node $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      (
        ( NTP4VCNode s l x r ) e. H
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

  ntp4vc-occ-node $e |- A. x e. U A. s e. ZZ
    A. l e. T A. y e. U A. r e. T
      (
        O ` <. x , ( NTP4VCNode s l y r ) >.
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

  ntp4vc-size-node $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      (
        S ` ( NTP4VCNode s l x r )
      )
      =
      (
        ( 1 + ( S ` l ) )
        +
        ( S ` r )
      ) $.

  $( Integer-valued rank equations. $)
  ntp4vc-rank-empty $e |- ( K ` NTP4VCEmpty ) = 0 $.

  ntp4vc-rank-node $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      (
        K ` ( NTP4VCNode s l x r )
      )
      =
      (
        1
        +
        ( NTP4VCMin ( K ` l ) ( K ` r ) )
      ) $.

  $( leftist equations. $)
  ntp4vc-leftist-empty $e |- NTP4VCEmpty e. I $.

  ntp4vc-leftist-node $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      (
        ( NTP4VCNode s l x r ) e. I
        <->
        (
          s = ( K ` ( NTP4VCNode s l x r ) )
          /\
          (
            l e. I
            /\
            (
              r e. I
              /\
              ( K ` r ) <_ ( K ` l )
            )
          )
        )
      ) $.

  $( The source minimum specification on every nonempty tree. $)
  ntp4vc-minimum-node $e |- A. s e. ZZ A. l e. T
    A. x e. U A. r e. T
      ( M ` ( NTP4VCNode s l x r ) ) = x $.

  $( Source theorem parameters A=h1 and B=h2, followed by fact0 and fact1. $)
  ntp4vc-h1-tree $e |- A e. T $.
  ntp4vc-h2-tree $e |- B e. T $.
  ntp4vc-fact0 $e |- ( NTP4VCLeftistHeap A H I ) $.
  ntp4vc-fact1 $e |- ( NTP4VCLeftistHeap B H I ) $.

  ntp4vc-pearl-leftist-heap-merge-vc $a |- (
    ( NTP4VCMergeEntry A B T U D L H O S I )
    /\
    A. q e. T
      (
        (
          NTP4VCMergeResultAntecedent
            q A B T U D H O S I M
        )
        ->
        (
          ( S ` q ) = ( ( S ` A ) + ( S ` B ) )
          /\
          (
            A. x e. U
              (
                O ` <. x , q >.
              )
              =
              (
                ( O ` <. x , A >. )
                +
                ( O ` <. x , B >. )
              )
            /\
            ( NTP4VCLeftistHeap q H I )
          )
        )
      )
  ) $.
$}
