$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/pairing_heap_PairingHeap_delete_minqtvc: the pairing-heap delete-min
  verification condition exposes the root's finite child-tree list and states
  that any result representing that list removes exactly one occurrence of
  the original minimum, preserves every other occurrence, and decreases the
  size by one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt and D is its total
  preorder. T is exactly the source inductive carrier of finite rose trees
  whose nodes contain an element of U and an arbitrary finite word of child
  trees. NTP4VCTree is an injective tagged constructor; closure,
  exhaustiveness, and structural induction exclude missing finite trees,
  extraneous values, and non-well-founded trees.

  R is exactly the source raw_heap sum type. NTP4VCEmpty and NTP4VCHeap are
  disjoint injective tagged constructors, with the latter carrying a member
  of T. L, H, J, K, S, F, G, O, Q, W, M, and N represent le_roots, heap,
  heap_tree, heap_list, size_heap, size_tree, size_list, occ_heap, occ_tree,
  occ_list, minimum, and minimum_tree. Their equations below are the complete
  source definitions over SetMM finite words and the full integer domain ZZ.

  V is the source record type heap1 and P is its raw-heap projection h.
  Nonemptiness, the heap invariant, and projection injectivity preserve the
  source record semantics without replacing records by weaker tags.

  Both source matches on h hh are expanded by existentially exposing the
  unique root element and child-tree word. The decomposition witnesses remain
  internal to the matched formulas, and the result heap remains universally
  quantified. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c NTP4VCTree NTP4VCEmpty NTP4VCHeap $.

ntp4vc-tree-syntax $a class ( NTP4VCTree A B ) $.
ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-heap-syntax $a class ( NTP4VCHeap A ) $.

ntp4vc-tree-def $a |- ( NTP4VCTree A B ) =
  <. 0 , <. A , B >. >. $.

ntp4vc-empty-def $a |- NTP4VCEmpty =
  <. 1 , (/) >. $.

ntp4vc-heap-def $a |- ( NTP4VCHeap A ) =
  <. 2 , A >. $.

${
  $d c e l p q r s t u v x y z
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

  $( Exact finite inductive rose-tree carrier over U. $)
  ntp4vc-tree-constructor-closure $e |- A. x e. U
    A. l e. Word T
      ( NTP4VCTree x l ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    E. x e. U E. l e. Word T
      t = ( NTP4VCTree x l ) $.

  ntp4vc-tree-structural-induction $e |- A. q e. ~P T
    (
      A. x e. U A. l e. Word T
        (
          ran l C_ q
          ->
          ( NTP4VCTree x l ) e. q
        )
      ->
      q = T
    ) $.

  $( Exact raw_heap carrier with constructors E and H. $)
  ntp4vc-raw-heap-empty-closure $e |- NTP4VCEmpty e. R $.

  ntp4vc-raw-heap-node-closure $e |- A. t e. T
    ( NTP4VCHeap t ) e. R $.

  ntp4vc-raw-heap-constructor-exhaustive $e |- A. r e. R
    (
      r = NTP4VCEmpty
      \/
      E. t e. T
        r = ( NTP4VCHeap t )
    ) $.

  $( Types of the source recursive predicates and functions used by the VC. $)
  ntp4vc-le-roots-relation
    $e |- L C_ ( U X. Word T ) $.
  ntp4vc-heap-predicate
    $e |- H C_ R $.
  ntp4vc-heap-tree-predicate
    $e |- J C_ T $.
  ntp4vc-heap-list-predicate
    $e |- K C_ Word T $.

  ntp4vc-size-heap-function
    $e |- S e. ( ZZ ^m R ) $.
  ntp4vc-size-tree-function
    $e |- F e. ( ZZ ^m T ) $.
  ntp4vc-size-list-function
    $e |- G e. ( ZZ ^m Word T ) $.

  ntp4vc-occ-heap-function
    $e |- O e. ( ZZ ^m ( U X. R ) ) $.
  ntp4vc-occ-tree-function
    $e |- Q e. ( ZZ ^m ( U X. T ) ) $.
  ntp4vc-occ-list-function
    $e |- W e. ( ZZ ^m ( U X. Word T ) ) $.

  ntp4vc-minimum-function
    $e |- M e. ( U ^m R ) $.
  ntp4vc-minimum-tree-function
    $e |- N e. ( U ^m T ) $.

  $( le_roots equations. $)
  ntp4vc-le-roots-empty $e |- A. e e. U
    <. e , (/) >. e. L $.

  ntp4vc-le-roots-cons $e |- A. e e. U A. x e. U
    A. c e. Word T A. r e. Word T
      (
        <.
          e ,
          ( <" ( NTP4VCTree x c ) "> ++ r )
        >. e. L
        <->
        (
          <. e , x >. e. D
          /\
          <. e , r >. e. L
        )
      ) $.

  $( heap, heap_tree, and heap_list equations. $)
  ntp4vc-heap-empty $e |- NTP4VCEmpty e. H $.

  ntp4vc-heap-node $e |- A. t e. T
    (
      ( NTP4VCHeap t ) e. H
      <->
      t e. J
    ) $.

  ntp4vc-heap-tree-def $e |- A. x e. U A. l e. Word T
    (
      ( NTP4VCTree x l ) e. J
      <->
      (
        <. x , l >. e. L
        /\
        l e. K
      )
    ) $.

  ntp4vc-heap-list-empty $e |- (/) e. K $.

  ntp4vc-heap-list-cons $e |- A. t e. T A. r e. Word T
    (
      ( <" t "> ++ r ) e. K
      <->
      (
        t e. J
        /\
        r e. K
      )
    ) $.

  $( Integer-valued size equations. $)
  ntp4vc-size-heap-empty $e |-
    ( S ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-heap-node $e |- A. t e. T
    (
      S ` ( NTP4VCHeap t )
    )
    =
    ( F ` t ) $.

  ntp4vc-size-tree-def $e |- A. x e. U A. l e. Word T
    (
      F ` ( NTP4VCTree x l )
    )
    =
    (
      1
      +
      ( G ` l )
    ) $.

  ntp4vc-size-list-empty $e |-
    ( G ` (/) ) = 0 $.

  ntp4vc-size-list-cons $e |- A. t e. T A. r e. Word T
    (
      G ` ( <" t "> ++ r )
    )
    =
    (
      ( F ` t )
      +
      ( G ` r )
    ) $.

  $( Integer-valued occurrence-count equations. $)
  ntp4vc-occ-heap-empty $e |- A. e e. U
    ( O ` <. e , NTP4VCEmpty >. ) = 0 $.

  ntp4vc-occ-heap-node $e |- A. e e. U A. t e. T
    (
      O ` <. e , ( NTP4VCHeap t ) >.
    )
    =
    (
      Q ` <. e , t >.
    ) $.

  ntp4vc-occ-tree-def $e |- A. e e. U A. x e. U
    A. l e. Word T
      (
        Q ` <. e , ( NTP4VCTree x l ) >.
      )
      =
      (
        if ( e = x , 1 , 0 )
        +
        ( W ` <. e , l >. )
      ) $.

  ntp4vc-occ-list-empty $e |- A. e e. U
    ( W ` <. e , (/) >. ) = 0 $.

  ntp4vc-occ-list-cons $e |- A. e e. U A. t e. T
    A. r e. Word T
      (
        W ` <. e , ( <" t "> ++ r ) >.
      )
      =
      (
        ( Q ` <. e , t >. )
        +
        ( W ` <. e , r >. )
      ) $.

  $( Source minimum equations; minimum on E remains intentionally unspecified. $)
  ntp4vc-minimum-tree-def $e |- A. x e. U A. l e. Word T
    (
      N ` ( NTP4VCTree x l )
    )
    =
    x $.

  ntp4vc-minimum-node $e |- A. t e. T
    (
      M ` ( NTP4VCHeap t )
    )
    =
    ( N ` t ) $.

  $( Source heap1 record carrier, projection, invariant, and extensionality. $)
  ntp4vc-heap1-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-heap1-projection
    $e |- P e. ( R ^m V ) $.

  ntp4vc-heap1-invariant $e |- A. p e. V
    ( P ` p ) e. H $.

  ntp4vc-heap1-extensionality $e |- A. p e. V A. q e. V
    (
      ( P ` p ) = ( P ` q )
      ->
      p = q
    ) $.

  $( Source theorem parameter A=hh, followed by fact0. $)
  ntp4vc-hh-heap $e |- A e. V $.
  ntp4vc-fact0 $e |- 0 < ( S ` ( P ` A ) ) $.

  ntp4vc-pearl-pairing-heap-delete-min-vc $a |- (
    (
      E. x e. U E. l e. Word T
        (
          ( P ` A )
          =
          ( NTP4VCHeap ( NTP4VCTree x l ) )
          /\
          l e. K
        )
    )
    /\
    A. p e. V
      (
        (
          E. x e. U E. l e. Word T
            (
              ( P ` A )
              =
              ( NTP4VCHeap ( NTP4VCTree x l ) )
              /\
              (
                ( S ` ( P ` p ) ) = ( G ` l )
                /\
                A. y e. U
                  (
                    O ` <. y , ( P ` p ) >.
                  )
                  =
                  (
                    W ` <. y , l >.
                  )
              )
            )
        )
        ->
        (
          (
            O ` <. ( M ` ( P ` A ) ) , ( P ` p ) >.
          )
          =
          (
            (
              O ` <. ( M ` ( P ` A ) ) , ( P ` A ) >.
            )
            -
            1
          )
          /\
          (
            A. y e. U
              (
                y =/= ( M ` ( P ` A ) )
                ->
                (
                  O ` <. y , ( P ` p ) >.
                )
                =
                (
                  O ` <. y , ( P ` A ) >.
                )
              )
            /\
            (
              S ` ( P ` p )
            )
            =
            (
              ( S ` ( P ` A ) )
              -
              1
            )
          )
        )
      )
  ) $.
$}
