$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/leftist_heap_LeftistHeap_delete_minqtvc: the leftist-heap delete-min
  verification condition exposes the two leftist subheaps and states that
  their merged result removes exactly one occurrence of the minimum while
  preserving all other occurrences, size, and the heap invariant. This file
  contains no proof.
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
  NTP4VCMin and NTP4VCLeftistHeap are faithful definitional expansions of
  integer minimum and the conjunction is_heap /\ leftist.

  Both source matches on h are expanded by existentially exposing the unique
  Node rank, left subtree, root element, and right subtree. The result remains
  universally quantified, and the decomposition witnesses remain internal to
  the antecedent of its implication. The final $a declaration is Metamath's
  native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode NTP4VCMin NTP4VCLeftistHeap
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C D ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-leftist-heap-syntax
  $a wff ( NTP4VCLeftistHeap A B C ) $.

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
  $d e l q r s t u v x y z
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

  $( Source theorem parameter A=h, followed by fact0 and fact1. $)
  ntp4vc-h-tree $e |- A e. T $.
  ntp4vc-fact0 $e |- 0 < ( S ` A ) $.
  ntp4vc-fact1 $e |- ( NTP4VCLeftistHeap A H I ) $.

  ntp4vc-pearl-leftist-heap-delete-min-vc $a |- (
    (
      E. s e. ZZ E. l e. T E. x e. U E. r e. T
        (
          A = ( NTP4VCNode s l x r )
          /\
          (
            ( NTP4VCLeftistHeap l H I )
            /\
            ( NTP4VCLeftistHeap r H I )
          )
        )
    )
    /\
    A. q e. T
      (
        (
          E. s e. ZZ E. l e. T E. x e. U E. r e. T
            (
              A = ( NTP4VCNode s l x r )
              /\
              (
                ( S ` q ) = ( ( S ` l ) + ( S ` r ) )
                /\
                (
                  A. y e. U
                    (
                      O ` <. y , q >.
                    )
                    =
                    (
                      ( O ` <. y , l >. )
                      +
                      ( O ` <. y , r >. )
                    )
                  /\
                  ( NTP4VCLeftistHeap q H I )
                )
              )
            )
        )
        ->
        (
          ( O ` <. ( M ` A ) , q >. )
          =
          ( ( O ` <. ( M ` A ) , A >. ) - 1 )
          /\
          (
            A. y e. U
              (
                y =/= ( M ` A )
                ->
                ( O ` <. y , q >. ) = ( O ` <. y , A >. )
              )
            /\
            (
              ( S ` q ) = ( ( S ` A ) - 1 )
              /\
              ( NTP4VCLeftistHeap q H I )
            )
          )
        )
      )
  ) $.
$}
